use once_cell::sync::Lazy;

use super::{
    heap::{DRAMHeap, HeapManager, MemType, PMHeap},
    list_node::AtomicListNode,
};
use crate::{
    error::AllocError,
    utils::{poison_memory_region, unpoison_memory_region, PM_PAGE_SIZE},
};
use std::{
    alloc::Layout,
    sync::{
        atomic::{AtomicPtr, Ordering},
        Mutex,
    },
};

// 1GB heap size
const HEAP_SIZE: usize = 1024 * 1024 * 1024;

/// Block size to use
///
/// The sizes must be power of two because they are also used for block alignment
/// We allow up to 2MB blocks (PM_PAGE_SIZE)
const BLOCK_SIZES: &[usize] = &[
    8,
    16,
    32,
    64,
    128,
    256,
    512,
    1024,
    2048,
    4096,
    4096 * 2,
    4096 * 4,
    4096 * 8,
    4096 * 16,
    4096 * 32,
    4096 * 64,
    4096 * 128,
    4096 * 256,
    4096 * 512,
];

fn list_index(layout: &Layout) -> Option<usize> {
    let required_block_size = layout.size().max(layout.align());

    // This is not the most efficient way, we might want to optimize it if necessary
    BLOCK_SIZES.iter().position(|&s| s >= required_block_size)
}

pub struct Allocator {
    dram: AllocInner<DRAMHeap>,
    pm: AllocInner<PMHeap>,
}

impl Allocator {
    pub fn get() -> &'static Allocator {
        static ALLOCATOR: Lazy<Allocator> = Lazy::new(|| Allocator {
            dram: AllocInner::<DRAMHeap>::new(),
            pm: AllocInner::<PMHeap>::new(),
        });
        &ALLOCATOR
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
    pub unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout, mem_type: MemType) {
        match mem_type {
            MemType::DRAM => self.dram.dealloc_inner(ptr, layout),
            MemType::PM => self.pm.dealloc_inner(ptr, layout),
        }
    }
}

pub(crate) struct AllocInner<T: HeapManager> {
    list_heads: [AtomicPtr<AtomicListNode>; BLOCK_SIZES.len()],
    heap_manager: Mutex<T>,
}

impl AllocInner<DRAMHeap> {
    pub(crate) fn new() -> Self {
        Self::with_capacity(HEAP_SIZE)
    }

    pub(crate) fn with_capacity(cap: usize) -> Self {
        AllocInner {
            list_heads: Default::default(),
            heap_manager: Mutex::new(DRAMHeap::new(cap)),
        }
    }
}

impl AllocInner<PMHeap> {
    pub(crate) fn new() -> Self {
        Self::with_capacity(HEAP_SIZE)
    }

    pub(crate) fn with_capacity(cap: usize) -> Self {
        assert!(cap >= PM_PAGE_SIZE);

        AllocInner {
            list_heads: Default::default(),
            heap_manager: Mutex::new(PMHeap::new(cap)),
        }
    }
}

impl<T: HeapManager> AllocInner<T> {
    /// Create a safe wrapper around alloc
    pub(crate) fn safe_alloc(&self, layout: Layout) -> Result<*mut u8, AllocError> {
        let size_class = list_index(&layout);
        match size_class {
            Some(index) => {
                let mut node = self.list_heads[index].load(Ordering::Acquire);
                loop {
                    if !node.is_null() {
                        unpoison_memory_region(node as *const u8, layout.size());
                        let new = unsafe { (*node).next.load(Ordering::Acquire) };
                        match self.list_heads[index].compare_exchange_weak(
                            node,
                            new,
                            Ordering::Acquire,
                            Ordering::Acquire,
                        ) {
                            Ok(_) => return Ok(node as *mut AtomicListNode as *mut u8),
                            Err(v) => {
                                node = v;
                                poison_memory_region(node as *const u8, layout.size());
                                continue;
                            }
                        }
                    }

                    assert!(std::mem::size_of::<AtomicListNode>() <= BLOCK_SIZES[index]);
                    assert!(std::mem::align_of::<AtomicListNode>() <= BLOCK_SIZES[index]);

                    let page_size = PM_PAGE_SIZE;
                    let page_align = page_size;
                    let page_layout = Layout::from_size_align(page_size, page_align).unwrap();

                    let page_mem = unsafe {
                        let mut heap_manager = self.heap_manager.lock().unwrap();
                        heap_manager.alloc_frame(page_layout)?
                    };

                    let mut node_n = AtomicListNode {
                        next: AtomicPtr::default(),
                    };
                    let block_size = BLOCK_SIZES[index];

                    for offset in (0..PM_PAGE_SIZE).step_by(block_size).rev() {
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
                        node,
                        new_node,
                        Ordering::Acquire,
                        Ordering::Acquire,
                    ) {
                        Ok(_) => {
                            return Ok(page_mem as *mut u8);
                        }
                        Err(v) => {
                            node = v;
                            unsafe {
                                self.heap_manager
                                    .lock()
                                    .unwrap()
                                    .dealloc_frame(page_mem, page_layout);
                            }
                            continue;
                        }
                    }
                }
            }
            None => {
                debug_assert!(layout.size() > PM_PAGE_SIZE);
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
                loop {
                    let new_node = AtomicListNode {
                        next: AtomicPtr::new(next),
                    };
                    debug_assert!(std::mem::size_of::<AtomicListNode>() <= BLOCK_SIZES[index]);
                    debug_assert!(std::mem::align_of::<AtomicListNode>() <= BLOCK_SIZES[index]);
                    let new_node_ptr = AtomicListNode::from_u8_ptr_unchecked(ptr);
                    unsafe { new_node_ptr.write(new_node) };
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
        heap::{DRAMHeap, HeapManager, PMHeap},
        utils::PM_PAGE_SIZE,
    };
    use std::alloc::Layout;

    fn basic_alloc_inner<H: HeapManager>(alloc: AllocInner<H>) {
        let alloc_layout = Layout::from_size_align(64, 64).unwrap();
        let max_cnt = PM_PAGE_SIZE / alloc_layout.size();

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

        // now we cannot allocate any more
        assert!(alloc.safe_alloc(alloc_layout).is_err());

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
        let alloc = AllocInner::<DRAMHeap>::with_capacity(PM_PAGE_SIZE);
        basic_alloc_inner(alloc);
    }

    #[test]
    fn pm_inner() {
        let alloc = AllocInner::<PMHeap>::with_capacity(PM_PAGE_SIZE);
        basic_alloc_inner(alloc);
    }
}
