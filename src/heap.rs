use crate::{
    error::AllocError,
    utils::mmap::{create_and_map_pool, map_dram_builder, unmap_memory},
};

use super::{list_node::ListNode, PM_PAGE_SIZE};
use std::{
    alloc::Layout,
    collections::HashMap,
    path::{Path, PathBuf},
};

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum MemType {
    DRAM,
    PM,
}

/// To deallocate the memory we need a way to tell the memory type,
/// i.e. we need to know where it comes from, {local, remote} {DRAM PM}
/// The easiest way is to partition the virtual memory address.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
#[allow(clippy::enum_clike_unportable_variant)]
pub(crate) enum MemAddrRange {
    DRAM = 0x5a00_0000_0000,
    PM = 0x5d00_0000_0000,
}

impl MemAddrRange {
    pub fn from_mem_type(t: MemType) -> Self {
        match t {
            MemType::PM => MemAddrRange::PM,
            MemType::DRAM => MemAddrRange::DRAM,
        }
    }
}

/// This struct manages all the small memory allocation,
/// manages the materialized memory heap
struct InnerHeap {
    heap_start: *mut u8,
    heap_size: usize,
    head: ListNode,
    high_addr: *mut u8,
}

impl InnerHeap {
    fn expand_free_page(&mut self) -> Result<*mut u8, AllocError> {
        let page_start = self.high_addr;
        if page_start as *const u8 == self.heap_end() {
            return Err(AllocError::OutOfMemory);
        }
        self.high_addr = unsafe { self.high_addr.add(PM_PAGE_SIZE) };
        Ok(page_start as *mut u8)
    }

    fn heap_end(&self) -> *const u8 {
        unsafe { self.heap_start.add(self.heap_size) }
    }

    fn add_free_page(&mut self, addr: *mut u8) {
        let mut node = ListNode::new();
        node.next = self.head.next.take();

        let node_ptr = ListNode::from_u8_ptr_unchecked(addr);
        unsafe { node_ptr.write(node) };
        self.head.next = Some(unsafe { &mut *node_ptr });
    }
}

pub(crate) trait HeapManager: Send + Sync {
    fn new(heap_size: usize) -> Self;

    /// # Safety
    /// Allocates frame using mmap is unsafe
    unsafe fn alloc_frame(&mut self, layout: Layout) -> Result<*mut u8, AllocError>;

    /// # Safety
    /// Deallocate memory is unsafe
    unsafe fn dealloc_frame(&mut self, ptr: *mut u8, layout: Layout);

    fn mem_addr_range(&self) -> MemAddrRange;
}

pub struct PMHeap {
    inner_heap: InnerHeap,
    /// High address in current virtual memory partition
    virtual_high_addr: *mut u8,
    files: HashMap<*mut u8, PathBuf>,
}

unsafe impl Send for PMHeap {}
unsafe impl Sync for PMHeap {}

impl HeapManager for PMHeap {
    fn new(heap_size: usize) -> Self {
        let virtual_high_addr = MemAddrRange::from_mem_type(MemType::PM) as usize as *mut u8;

        let mut manager = PMHeap {
            inner_heap: InnerHeap {
                heap_size,
                high_addr: virtual_high_addr,
                head: ListNode::new(),
                heap_start: virtual_high_addr,
            },
            virtual_high_addr,
            files: HashMap::new(),
        };

        // init the frame
        let layout = Layout::from_size_align(heap_size, PM_PAGE_SIZE).unwrap();
        manager.alloc_large(layout).unwrap();

        manager
    }

    unsafe fn alloc_frame(&mut self, layout: Layout) -> Result<*mut u8, AllocError> {
        let size = layout.size();
        if size <= PM_PAGE_SIZE {
            self.alloc_small(layout)
        } else {
            self.alloc_large(layout)
        }
    }

    unsafe fn dealloc_frame(&mut self, ptr: *mut u8, layout: Layout) {
        let size = layout.size();
        if size <= PM_PAGE_SIZE {
            self.inner_heap.add_free_page(ptr);
        } else {
            self.dealloc_large(ptr, layout);
        }
    }

    fn mem_addr_range(&self) -> MemAddrRange {
        MemAddrRange::from_mem_type(MemType::PM)
    }
}

impl PMHeap {
    /// Allocate pages from heap
    fn alloc_small(&mut self, _layout: Layout) -> Result<*mut u8, AllocError> {
        if let Some(head_next) = self.inner_heap.head.next.take() {
            self.inner_heap.head.next = head_next.next.take();
            Ok(head_next.start_address() as *mut u8)
        } else {
            self.inner_heap.expand_free_page()
        }
    }

    pub fn alloc_large_from(
        &mut self,
        layout: Layout,
        pool_dir: &String,
    ) -> Result<*mut u8, AllocError> {
        let aligned_size = align_up(layout.size(), PM_PAGE_SIZE);

        std::fs::create_dir_all(pool_dir).unwrap();

        let unix_time = std::time::SystemTime::now()
            .duration_since(std::time::SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64;
        let pool_path = Path::new(pool_dir).join(format!("pool-{}", unix_time));

        let next_addr = self.virtual_high_addr;
        self.virtual_high_addr = unsafe { self.virtual_high_addr.add(aligned_size) };

        let addr = create_and_map_pool(&pool_path, aligned_size, Some(next_addr))
            .map_err(|_e| AllocError::MmapFail)?;
        self.files.insert(addr, pool_path);
        Ok(addr)
    }

    fn alloc_large(&mut self, layout: Layout) -> Result<*mut u8, AllocError> {
        let base_str =
            std::env::var("POOL_DIR").unwrap_or_else(|_| "target/memory_pool".to_string());
        self.alloc_large_from(layout, &base_str)
    }

    fn dealloc_large(&mut self, ptr: *mut u8, layout: Layout) {
        let val = if let Some(v) = self.files.get(&ptr) {
            v.clone()
        } else {
            panic!("trying to deallocate a non-allocated memory");
        };

        self.files.remove(&ptr);

        let aligned_size = align_up(layout.size(), PM_PAGE_SIZE);

        unsafe {
            unmap_memory(ptr, aligned_size);
        }

        std::fs::remove_file(val).unwrap();
    }
}

impl Drop for PMHeap {
    fn drop(&mut self) {
        for (_ptr, t) in self.files.iter() {
            std::fs::remove_file(t).unwrap();
        }
    }
}

pub struct DRAMHeap {
    inner_heap: InnerHeap,
    virtual_high_addr: *mut u8,
}

unsafe impl Send for DRAMHeap {}
unsafe impl Sync for DRAMHeap {}

impl HeapManager for DRAMHeap {
    fn new(heap_size: usize) -> Self {
        let addr = MemAddrRange::from_mem_type(MemType::DRAM) as usize as *const u8;

        let heap_start = DRAMHeap::map_dram_pool(heap_size, Some(addr as *const u8))
            .expect("failed to create DRAM heap pool!");
        let inner_heap = InnerHeap {
            heap_size,
            heap_start,
            high_addr: heap_start,
            head: ListNode::new(),
        };
        DRAMHeap {
            inner_heap,
            virtual_high_addr: unsafe { heap_start.add(heap_size) },
        }
    }

    /// # Safety
    /// unsafe because the layout can be anything
    unsafe fn alloc_frame(&mut self, layout: Layout) -> Result<*mut u8, AllocError> {
        let size = layout.size();
        if size <= PM_PAGE_SIZE {
            self.alloc_small(layout)
        } else {
            self.alloc_large(layout)
        }
    }

    /// # Safety
    /// unsafe because the pointer can be anything, e.g. dealloc any memory pages
    unsafe fn dealloc_frame(&mut self, ptr: *mut u8, layout: Layout) {
        debug_assert!(std::mem::size_of::<ListNode>() <= layout.size());
        debug_assert!(std::mem::align_of::<ListNode>() <= layout.align());

        let size = layout.size();
        if size <= PM_PAGE_SIZE {
            self.inner_heap.add_free_page(ptr)
        } else {
            self.dealloc_large(ptr, layout)
        }
    }

    fn mem_addr_range(&self) -> MemAddrRange {
        MemAddrRange::from_mem_type(MemType::DRAM)
    }
}

impl DRAMHeap {
    /// Create a new memory mapping for huge memory (> 2MB)
    fn alloc_large(&mut self, layout: Layout) -> Result<*mut u8, AllocError> {
        let aligned_size = align_up(layout.size(), PM_PAGE_SIZE);
        let next_addr = self.virtual_high_addr;
        self.virtual_high_addr = unsafe { self.virtual_high_addr.add(aligned_size) };
        DRAMHeap::map_dram_pool(aligned_size, Some(next_addr))
    }

    fn map_dram_pool(heap_size: usize, addr: Option<*const u8>) -> Result<*mut u8, AllocError> {
        map_dram_builder(heap_size, addr, None)
            .map()
            .map_err(|_e| AllocError::MmapFail)
    }

    fn dealloc_large(&mut self, ptr: *mut u8, layout: Layout) {
        let aligned_size = align_up(layout.size(), PM_PAGE_SIZE);

        unsafe {
            unmap_memory(ptr, aligned_size);
        }
    }

    /// Allocate pages from heap
    fn alloc_small(&mut self, _layout: Layout) -> Result<*mut u8, AllocError> {
        if let Some(head_next) = self.inner_heap.head.next.take() {
            self.inner_heap.head.next = head_next.next.take();
            Ok(head_next.start_address() as *mut u8)
        } else {
            self.inner_heap.expand_free_page()
        }
    }
}

/// Align the given address `size` upwards to alignment `align`.
///
/// Requires that `align` is a power of two.
fn align_up(size: usize, align: usize) -> usize {
    (size + align - 1) & !(align - 1)
}

#[cfg(test)]
mod tests {
    use super::{DRAMHeap, HeapManager, PMHeap};
    use crate::PM_PAGE_SIZE;
    use std::alloc::Layout;

    fn basic_heap_alloc<H: HeapManager>() {
        let page_cnt = 16;
        let mut heap = H::new(PM_PAGE_SIZE * page_cnt);
        let addr_range = heap.mem_addr_range();

        let page_layout = Layout::from_size_align(PM_PAGE_SIZE, PM_PAGE_SIZE).unwrap();

        // allocate all pages
        let mut allocated = vec![];
        for _i in 0..page_cnt {
            let ptr = unsafe { heap.alloc_frame(page_layout).unwrap() };
            assert_eq!(ptr as usize % PM_PAGE_SIZE, 0);
            assert_eq!(ptr as usize & addr_range as usize, addr_range as usize);
            allocated.push(ptr);
        }

        // can't allocate more
        unsafe {
            assert!(heap.alloc_frame(page_layout).is_err());
        }

        // deallocate them
        for ptr in allocated {
            unsafe {
                heap.dealloc_frame(ptr, page_layout);
            }
        }

        // can allocate again
        let mut allocated = vec![];
        for _i in 0..page_cnt {
            let ptr = unsafe { heap.alloc_frame(page_layout).unwrap() };
            assert_eq!(ptr as usize % PM_PAGE_SIZE, 0);
            allocated.push(ptr);
        }
    }

    #[test]
    fn dram_heap() {
        basic_heap_alloc::<DRAMHeap>();
    }

    #[test]
    fn pm_heap() {
        basic_heap_alloc::<PMHeap>();
    }
}
