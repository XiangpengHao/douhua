use super::{
    heap::{DRAMHeap, HeapManager, PMHeap},
    list_node::AtomicListNode,
};
use crate::{
    error::AllocError,
    heap::MemAddrRange,
    utils::{
        backoff::Backoff, list_index, poison_memory_region, unpoison_memory_region, MemType,
        BLOCK_SIZES, PAGE_SIZE,
    },
};
use nanorand::Rng;
use once_cell::sync::OnceCell;
use std::alloc::Layout;
use std::sync::Mutex;

#[cfg(all(feature = "shuttle", test))]
use shuttle::sync::atomic::{AtomicPtr, Ordering};

#[cfg(not(all(feature = "shuttle", test)))]
use std::sync::atomic::{AtomicPtr, Ordering};

pub struct Allocator {
    dram: AllocInner<DRAMHeap>,
    pm: AllocInner<PMHeap>,
}

#[cfg(feature = "shard-6")]
const SHARD_NUM: usize = 6;

#[cfg(not(feature = "shard-6"))]
const SHARD_NUM: usize = 1;

static ALLOCATOR: once_cell::sync::OnceCell<[Allocator; SHARD_NUM]> = OnceCell::new();

impl Allocator {
    pub fn get() -> &'static Allocator {
        let allocator = ALLOCATOR.get_or_init(|| {
            let mem_each_shard = 1024 * 1024 * 1024 * 32; // 128 GB

            let mut allocators: [std::mem::MaybeUninit<Allocator>; SHARD_NUM] =
                unsafe { std::mem::MaybeUninit::uninit().assume_init() };

            for (i, elem) in allocators.iter_mut().enumerate() {
                unsafe {
                    std::ptr::write(
                        elem.as_mut_ptr(),
                        Allocator {
                            dram: AllocInner::<DRAMHeap>::with_capacity(
                                (MemAddrRange::DRAM as usize + mem_each_shard * i) as *mut u8,
                            ),
                            pm: AllocInner::<PMHeap>::with_capacity(
                                (MemAddrRange::PM as usize + mem_each_shard * i) as *mut u8,
                            ),
                        },
                    );
                }
            }
            unsafe { std::mem::transmute::<_, [Allocator; SHARD_NUM]>(allocators) }
        });
        #[cfg(feature = "shard-6")]
        {
            let v = nanorand::tls_rng().generate_range(0..SHARD_NUM);
            unsafe { &allocator.get_unchecked(v) }
        }

        #[cfg(not(feature = "shard-6"))]
        {
            &allocator[0]
        }
    }

    /// # Safety
    /// unsafe inherit from GlobalAlloc
    pub unsafe fn alloc(&self, layout: Layout, mem_type: MemType) -> Result<*mut u8, AllocError> {
        match mem_type {
            MemType::DRAM => self.dram.safe_alloc(layout),
            MemType::PM => self.pm.safe_alloc(layout),
        }
    }

    /// # Safety
    /// unsafe inherit from GlobalAlloc
    pub unsafe fn alloc_zeroed(
        &self,
        layout: Layout,
        mem_type: MemType,
    ) -> Result<*mut u8, AllocError> {
        let ptr = match mem_type {
            MemType::DRAM => self.dram.safe_alloc(layout),
            MemType::PM => self.pm.safe_alloc(layout),
        }?;
        ptr.write_bytes(0, layout.size());
        Ok(ptr)
    }

    /// # Safety
    /// unsafe inherit from GlobalAlloc
    pub unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if self.dram.is_my_memory(ptr) {
            self.dram.dealloc_inner(ptr, layout)
        } else {
            assert!(self.pm.is_my_memory(ptr));
            self.pm.dealloc_inner(ptr, layout)
        }
    }
}

pub(crate) struct AllocInner<T: HeapManager> {
    list_heads: [AtomicPtr<AtomicListNode>; BLOCK_SIZES.len()],
    heap_manager: Mutex<T>,
}

impl AllocInner<DRAMHeap> {
    pub(crate) fn with_capacity(heap_start_addr: *mut u8) -> Self {
        AllocInner {
            list_heads: Default::default(),
            heap_manager: Mutex::new(DRAMHeap::new(heap_start_addr)),
        }
    }
}

impl AllocInner<PMHeap> {
    pub(crate) fn with_capacity(heap_start_addr: *mut u8) -> Self {
        AllocInner {
            list_heads: Default::default(),
            heap_manager: Mutex::new(PMHeap::new(heap_start_addr)),
        }
    }
}

impl<T: HeapManager> AllocInner<T> {
    /// Create a safe wrapper around alloc
    pub(crate) fn safe_alloc(&self, layout: Layout) -> Result<*mut u8, AllocError> {
        let size_class = list_index(&layout);
        match size_class {
            Some(index) => {
                let backoff = Backoff::new();
                let mut node = self.list_heads[index].load(Ordering::Acquire);
                loop {
                    // if node is locked, wait until other threads unlock it
                    if node as usize == usize::MAX {
                        backoff.spin();
                        node = self.list_heads[index].load(Ordering::Acquire);
                        continue;
                    }

                    if !node.is_null() {
                        let clean_node =
                            ((node as usize) & 0x0000_ffff_ffff_ffff) as *mut AtomicListNode; // untag the pointer
                        unpoison_memory_region(clean_node as *const u8, layout.size());
                        let new = unsafe { (*clean_node).next.load(Ordering::Acquire) };
                        match self.list_heads[index].compare_exchange_weak(
                            node,
                            new,
                            Ordering::Acquire,
                            Ordering::Acquire,
                        ) {
                            Ok(_) => return Ok(clean_node as *mut AtomicListNode as *mut u8),
                            Err(v) => {
                                node = v;
                                poison_memory_region(node as *const u8, layout.size());
                                backoff.spin();
                                continue;
                            }
                        }
                    }

                    // exclusively lock the list head
                    match self.list_heads[index].compare_exchange_weak(
                        node,
                        usize::MAX as *mut AtomicListNode,
                        Ordering::Acquire,
                        Ordering::Acquire,
                    ) {
                        Ok(_v) => {}
                        Err(v) => {
                            node = v;
                            backoff.spin();
                            continue;
                        }
                    }

                    assert!(std::mem::size_of::<AtomicListNode>() <= BLOCK_SIZES[index]);
                    assert!(std::mem::align_of::<AtomicListNode>() <= BLOCK_SIZES[index]);

                    let page_size = PAGE_SIZE;
                    let page_align = page_size;
                    let page_layout = Layout::from_size_align(page_size, page_align).unwrap();

                    let mut heap_manager = if let Ok(h) = self.heap_manager.try_lock() {
                        h
                    } else {
                        self.list_heads[index].store(node, Ordering::Release);
                        backoff.spin();
                        continue;
                    };

                    let page_mem = match unsafe { heap_manager.alloc_frame(page_layout) } {
                        Ok(v) => v,
                        Err(v) => {
                            self.list_heads[index].store(node, Ordering::Release);
                            return Err(v);
                        }
                    };

                    let mut node_n = AtomicListNode {
                        next: AtomicPtr::default(),
                    };
                    let block_size = BLOCK_SIZES[index];

                    for offset in (0..PAGE_SIZE).step_by(block_size).rev() {
                        unsafe {
                            let node_ptr =
                                AtomicListNode::from_u8_ptr_unchecked(page_mem.add(offset));
                            node_ptr.write(node_n);
                            node_n = AtomicListNode {
                                next: AtomicPtr::new(node_ptr),
                            };
                        }
                    }
                    let new_node = unsafe {
                        node_n
                            .next
                            .load(Ordering::Relaxed)
                            .read()
                            .next
                            .load(Ordering::Relaxed)
                    };
                    match self.list_heads[index].compare_exchange_weak(
                        usize::MAX as *mut AtomicListNode,
                        new_node,
                        Ordering::Acquire,
                        Ordering::Acquire,
                    ) {
                        Ok(_) => {
                            return Ok(page_mem as *mut u8);
                        }
                        Err(_v) => {
                            unreachable!("list node is locked, no one should contend with us")
                        }
                    }
                }
            }
            None => {
                debug_assert!(layout.size() > PAGE_SIZE);
                let mut heap_manager = self.heap_manager.lock().unwrap();
                unsafe { heap_manager.alloc_frame(layout) }
            }
        }
    }

    pub(crate) fn dealloc_inner(&self, ptr: *mut u8, layout: Layout) {
        assert!(
            self.is_my_memory(ptr),
            "dealloc ptr is not allocated by me!"
        );

        match list_index(&layout) {
            Some(index) => {
                let mut next = self.list_heads[index].load(Ordering::Acquire);
                let backoff = Backoff::new();
                loop {
                    if next as usize == usize::MAX {
                        // list head is locked, wait until other threads unlock it
                        backoff.spin();
                        next = self.list_heads[index].load(Ordering::Acquire);
                        continue;
                    }

                    let new_node = AtomicListNode {
                        next: AtomicPtr::new(next),
                    };

                    // Tag the pointer to prevent ABA problem
                    // TODO: maybe random number is too expensive, any simpler ways?
                    let tag: u8 = nanorand::tls_rng().generate_range(0..255);
                    let tag = (tag as usize) << 56;

                    debug_assert!(std::mem::size_of::<AtomicListNode>() <= BLOCK_SIZES[index]);
                    debug_assert!(std::mem::align_of::<AtomicListNode>() <= BLOCK_SIZES[index]);
                    let new_node_ptr = AtomicListNode::from_u8_ptr_unchecked(ptr);
                    unsafe { new_node_ptr.write(new_node) };
                    let new_node_ptr = (new_node_ptr as usize | tag) as *mut AtomicListNode;
                    match self.list_heads[index].compare_exchange_weak(
                        next,
                        new_node_ptr,
                        Ordering::Acquire,
                        Ordering::Acquire,
                    ) {
                        Ok(_) => {
                            poison_memory_region(ptr, layout.size());
                            break;
                        }
                        Err(v) => next = v,
                    };
                }
            }
            None => {
                let mut heap_manager = self.heap_manager.lock().unwrap();
                unsafe { heap_manager.dealloc_frame(ptr, layout) };
            }
        }
    }

    // test if a ptr is allocated by me
    fn is_my_memory(&self, ptr: *mut u8) -> bool {
        let range = T::mem_addr_range();
        (ptr as usize & range as usize) == range as usize
    }
}

#[cfg(test)]
mod tests {
    use super::AllocInner;
    use crate::{
        heap::{DRAMHeap, HeapManager, MemAddrRange, PMHeap},
        utils::PAGE_SIZE,
    };
    use std::alloc::Layout;

    fn basic_alloc_inner<H: HeapManager>(alloc: AllocInner<H>) {
        let alloc_layout = Layout::from_size_align(64, 64).unwrap();
        let max_cnt = PAGE_SIZE / alloc_layout.size();

        let mut allocated = vec![];

        // allocate all memory, the layout are aligned so we can use all the memory
        for i in 0..max_cnt {
            let ptr = alloc.safe_alloc(alloc_layout).unwrap();
            unsafe {
                for j in 0..alloc_layout.size() {
                    ptr.add(j).write(i as u8);
                }
            }
            allocated.push(ptr);
        }

        // check sanity and dealloc them
        for (i, ptr) in allocated.into_iter().enumerate() {
            for j in 0..alloc_layout.size() {
                assert_eq!(unsafe { ptr.add(j).read() }, i as u8);
            }
            alloc.dealloc_inner(ptr, alloc_layout);
        }

        // now we can allocate again
        for i in 0..max_cnt {
            let ptr = alloc.safe_alloc(alloc_layout).unwrap();
            unsafe {
                for j in 0..alloc_layout.size() {
                    ptr.add(j).write(i as u8);
                }
            }
        }
    }

    #[test]
    fn dram_inner() {
        let alloc = AllocInner::<DRAMHeap>::with_capacity(MemAddrRange::DRAM as usize as *mut u8);
        basic_alloc_inner(alloc);
    }

    #[test]
    fn pm_inner() {
        let alloc = AllocInner::<PMHeap>::with_capacity(MemAddrRange::PM as usize as *mut u8);
        basic_alloc_inner(alloc);
    }

    enum Operation {
        Alloc512,
        Alloc256,
        Alloc1024,
        Dealloc,
    }

    impl Operation {
        fn gen(rng: &mut impl Rng) -> Self {
            match rng.gen_range(0..4) {
                0 => Operation::Alloc256,
                1 => Operation::Alloc512,
                2 => Operation::Alloc1024,
                3 => Operation::Dealloc,
                _ => unreachable!(),
            }
        }
    }

    use std::sync::Arc;

    #[cfg(feature = "shuttle")]
    use shuttle::{
        rand::{thread_rng, Rng},
        thread,
    };

    #[cfg(not(feature = "shuttle"))]
    use ::{
        rand::{thread_rng, Rng},
        std::thread,
    };

    thread_local! {
        static THREAD_HEAP_START: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    }

    fn mt_basic(heap_addr: &std::sync::atomic::AtomicUsize) {
        let addr = THREAD_HEAP_START.with(|v| {
            let addr = v.load(std::sync::atomic::Ordering::Relaxed);
            if addr == 0 {
                let addr = heap_addr
                    .fetch_add(1024 * 1024 * 1024 * 8, std::sync::atomic::Ordering::SeqCst);
                v.store(addr, std::sync::atomic::Ordering::Relaxed);
                addr
            } else {
                addr
            }
        });
        let alloc = AllocInner::<DRAMHeap>::with_capacity(addr as *mut u8);
        let alloc = Arc::new(alloc);

        let allocated = Arc::new(crossbeam_queue::SegQueue::<(usize, usize)>::new());

        let thread_cnt = 3;
        let mut handlers = vec![];
        for _t in 0..thread_cnt {
            let allocated = allocated.clone();
            let alloc = alloc.clone();
            let h = thread::spawn(move || {
                let mut rng = thread_rng();

                let _tid = thread::current().id();

                for _i in 0..16 {
                    let layout = match Operation::gen(&mut rng) {
                        Operation::Alloc256 => Layout::from_size_align(256, 8).unwrap(),
                        Operation::Alloc512 => Layout::from_size_align(512, 8).unwrap(),
                        Operation::Alloc1024 => Layout::from_size_align(1024, 8).unwrap(),
                        Operation::Dealloc => {
                            if let Some((ptr, size)) = allocated.pop() {
                                let ptr = ptr as *mut u8;
                                for i in 0..size {
                                    let v = unsafe { ptr.add(i).read() };
                                    assert_eq!(v, size as u8);
                                }
                                alloc.dealloc_inner(ptr, Layout::from_size_align(size, 8).unwrap());
                            }
                            continue;
                        }
                    };
                    let ptr = alloc.safe_alloc(layout).unwrap();
                    for i in 0..layout.size() {
                        unsafe { ptr.add(i).write(layout.size() as u8) };
                    }
                    allocated.push((ptr as usize, layout.size()));
                }
            });
            handlers.push(h);
        }
        for h in handlers {
            h.join().unwrap();
        }
    }

    #[cfg(not(feature = "shuttle"))]
    #[test]
    fn mt_basic_test() {
        let heap_addr = std::sync::atomic::AtomicUsize::new(MemAddrRange::DRAM as usize);
        mt_basic(&heap_addr);
    }

    #[cfg(feature = "shuttle")]
    #[test]
    fn shuttle_mt_basic() {
        let config = shuttle::Config::default();
        let mut runner = shuttle::PortfolioRunner::new(true, config);
        runner.add(shuttle::scheduler::PctScheduler::new(5, 40_000));
        runner.add(shuttle::scheduler::RandomScheduler::new(40_000));

        let heap_addr = std::sync::atomic::AtomicUsize::new(MemAddrRange::DRAM as usize);

        runner.run(move || {
            mt_basic(&heap_addr);
        });
    }

    #[cfg(feature = "shuttle")]
    #[test]
    fn shuttle_replay() {
        let heap_addr = std::sync::atomic::AtomicUsize::new(MemAddrRange::DRAM as usize);
        shuttle::replay(
            move || mt_basic(&heap_addr),
            "910283019e879a8cd8b2fc86b80100f8532729521445164551e28b244531258ad292f4e7a4444aa448bd248a8b9448511245494b92480a000000000000000000",
        )
    }
}
