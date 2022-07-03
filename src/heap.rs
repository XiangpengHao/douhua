use crate::{
    error::AllocError,
    utils::{
        mmap::{create_and_map_pool, map_dram_builder, unmap_memory},
        MemType, PAGE_SIZE,
    },
};

use super::list_node::ListNode;
use std::{
    alloc::Layout,
    collections::HashMap,
    path::{Path, PathBuf},
};

/// To deallocate the memory we need a way to tell the memory type,
/// i.e. we need to know where it comes from, {local, remote} {DRAM PM}
/// The easiest way is to partition the virtual memory address.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
#[allow(clippy::upper_case_acronyms)]
#[allow(clippy::enum_clike_unportable_variant)]
pub(crate) enum MemAddrRange {
    DRAM = 0x5a00_0000_0000,
    PM = 0x5d00_0000_0000,
}

impl From<MemType> for MemAddrRange {
    fn from(t: MemType) -> Self {
        match t {
            MemType::PM => MemAddrRange::PM,
            MemType::DRAM => MemAddrRange::DRAM,
        }
    }
}

impl From<*const u8> for MemAddrRange {
    fn from(addr: *const u8) -> Self {
        let dram_range = MemAddrRange::DRAM as usize;
        if (addr as usize & dram_range) == dram_range {
            MemAddrRange::DRAM
        } else {
            assert!(
                ((addr as usize) & (MemAddrRange::PM as usize)) == MemAddrRange::PM as usize,
                "The memory address is not from Douhua! Something extremely bad happened!"
            );
            MemAddrRange::PM
        }
    }
}

/// This struct manages all the small memory allocation (2MB pages)
struct InnerHeap {
    heap_start: *mut u8,
    heap_size: usize,
    free_list: ListNode,
    high_addr: *mut u8,
}

impl InnerHeap {
    fn expand_free_page(&mut self) -> Result<*mut u8, AllocError> {
        let page_start = self.high_addr;
        if page_start as *const u8 == self.heap_end() {
            return Err(AllocError::OutOfMemory);
        }
        self.high_addr = unsafe { self.high_addr.add(PAGE_SIZE) };
        Ok(page_start as *mut u8)
    }

    fn heap_end(&self) -> *const u8 {
        unsafe { self.heap_start.add(self.heap_size) }
    }

    /// Add a 2MB page to the temporary free list
    fn add_free_page(&mut self, addr: *mut u8) {
        let mut node = ListNode::new();
        node.next = self.free_list.next.take();

        let node_ptr = ListNode::from_u8_ptr_unchecked(addr);
        unsafe { node_ptr.write(node) };
        self.free_list.next = Some(unsafe { &mut *node_ptr });
    }
}

pub(crate) trait HeapManager: Send + Sync {
    fn new(heap_start_addr: *mut u8) -> Self;

    /// # Safety
    /// Allocates frame using mmap is unsafe
    unsafe fn alloc_frame(&mut self, layout: Layout) -> Result<*mut u8, AllocError>;

    /// # Safety
    /// Deallocate memory is unsafe
    unsafe fn dealloc_frame(&mut self, ptr: *mut u8, layout: Layout);

    fn mem_addr_range() -> MemAddrRange;
}

pub struct PMHeap {
    inner_heap: InnerHeap,
    /// High address in current virtual memory partition
    virtual_high_addr: *mut u8,
    files: HashMap<*mut u8, PathBuf>,
}

unsafe impl Send for PMHeap {}
unsafe impl Sync for PMHeap {}

const PM_DEFAULT_ALLOC_SIZE: usize = 1024 * 1024 * 1024 * 4; // 2GB

impl HeapManager for PMHeap {
    fn new(heap_start_addr: *mut u8) -> Self {
        // let virtual_high_addr = MemAddrRange::from(MemType::PM) as usize as *mut u8;

        let mut manager = PMHeap {
            inner_heap: InnerHeap {
                heap_size: 0,
                high_addr: heap_start_addr,
                free_list: ListNode::new(),
                heap_start: heap_start_addr,
            },
            virtual_high_addr: heap_start_addr,
            files: HashMap::new(),
        };

        // init the frame
        let layout = Layout::from_size_align(PM_DEFAULT_ALLOC_SIZE, PAGE_SIZE).unwrap();
        manager.expand_heap(layout).unwrap();

        manager
    }

    unsafe fn alloc_frame(&mut self, layout: Layout) -> Result<*mut u8, AllocError> {
        let size = layout.size();
        if size <= PAGE_SIZE {
            assert_eq!(size, PAGE_SIZE);
            self.alloc_page(layout)
        } else {
            let base_str =
                std::env::var("POOL_DIR").unwrap_or_else(|_| "target/memory_pool".to_string());
            let rv = self.alloc_large_from(layout, &base_str)?;
            Ok(rv.0)
        }
    }

    unsafe fn dealloc_frame(&mut self, ptr: *mut u8, layout: Layout) {
        let size = layout.size();
        if size <= PAGE_SIZE {
            self.inner_heap.add_free_page(ptr);
        } else {
            self.dealloc_large(ptr, layout);
        }
    }

    fn mem_addr_range() -> MemAddrRange {
        MemAddrRange::from(MemType::PM)
    }
}

impl PMHeap {
    /// Allocate pages from heap
    fn alloc_page(&mut self, layout: Layout) -> Result<*mut u8, AllocError> {
        if let Some(head_next) = self.inner_heap.free_list.next.take() {
            self.inner_heap.free_list.next = head_next.next.take();
            Ok(head_next.start_address() as *mut u8)
        } else {
            let rv = self.inner_heap.expand_free_page();
            match rv {
                Ok(v) => Ok(v),
                Err(v) => {
                    assert!(matches!(v, AllocError::OutOfMemory));
                    let large_layout =
                        Layout::from_size_align(PM_DEFAULT_ALLOC_SIZE, PAGE_SIZE).unwrap();
                    self.expand_heap(large_layout).unwrap();
                    self.alloc_page(layout)
                }
            }
        }
    }

    fn alloc_large_from(
        &mut self,
        layout: Layout,
        pool_dir: &str,
    ) -> Result<(*mut u8, usize), AllocError> {
        let aligned_size = align_up(layout.size(), PAGE_SIZE);

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

        Ok((addr, aligned_size))
    }

    fn expand_heap(&mut self, layout: Layout) -> Result<*mut u8, AllocError> {
        let base_str =
            std::env::var("POOL_DIR").unwrap_or_else(|_| "target/memory_pool".to_string());
        let rv = self.alloc_large_from(layout, &base_str)?;
        self.inner_heap.heap_size += rv.1;
        Ok(rv.0)
    }

    fn dealloc_large(&mut self, ptr: *mut u8, layout: Layout) {
        let val = if let Some(v) = self.files.get(&ptr) {
            v.clone()
        } else {
            panic!("trying to deallocate a non-allocated memory");
        };

        self.files.remove(&ptr);

        let aligned_size = align_up(layout.size(), PAGE_SIZE);

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

const DRAM_DEFAULT_ALLOC_SIZE: usize = 1024 * 1024 * 8; // 512MB

impl HeapManager for DRAMHeap {
    fn new(heap_start_addr: *mut u8) -> Self {
        let heap_start_addr =
            DRAMHeap::map_dram_pool(DRAM_DEFAULT_ALLOC_SIZE, Some(heap_start_addr as *const u8))
                .expect("failed to create DRAM heap pool!");

        let inner_heap = InnerHeap {
            heap_size: DRAM_DEFAULT_ALLOC_SIZE,
            heap_start: heap_start_addr,
            high_addr: heap_start_addr,
            free_list: ListNode::new(),
        };

        DRAMHeap {
            inner_heap,
            virtual_high_addr: unsafe { heap_start_addr.add(DRAM_DEFAULT_ALLOC_SIZE) },
        }
    }

    /// # Safety
    /// unsafe because the layout can be anything
    unsafe fn alloc_frame(&mut self, layout: Layout) -> Result<*mut u8, AllocError> {
        let size = layout.size();
        if size <= PAGE_SIZE {
            self.alloc_page(layout)
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
        if size <= PAGE_SIZE {
            self.inner_heap.add_free_page(ptr)
        } else {
            self.dealloc_large(ptr, layout)
        }
    }

    fn mem_addr_range() -> MemAddrRange {
        MemAddrRange::from(MemType::DRAM)
    }
}

impl DRAMHeap {
    /// Create a new memory mapping for huge memory (> 2MB)
    fn alloc_large(&mut self, layout: Layout) -> Result<*mut u8, AllocError> {
        let aligned_size = align_up(layout.size(), PAGE_SIZE);
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
        let aligned_size = align_up(layout.size(), PAGE_SIZE);

        unsafe {
            unmap_memory(ptr, aligned_size);
        }
    }

    /// Allocate pages from heap
    fn alloc_page(&mut self, layout: Layout) -> Result<*mut u8, AllocError> {
        if let Some(head_next) = self.inner_heap.free_list.next.take() {
            self.inner_heap.free_list.next = head_next.next.take();
            Ok(head_next.start_address() as *mut u8)
        } else {
            match self.inner_heap.expand_free_page() {
                Ok(addr) => Ok(addr),
                Err(e) => {
                    assert!(matches!(e, AllocError::OutOfMemory));
                    self.alloc_large(
                        Layout::from_size_align(DRAM_DEFAULT_ALLOC_SIZE, PAGE_SIZE).unwrap(),
                    )?;
                    self.inner_heap.heap_size += DRAM_DEFAULT_ALLOC_SIZE;
                    self.alloc_page(layout)
                }
            }
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
    use crate::utils::PAGE_SIZE;

    use super::*;
    use std::alloc::Layout;

    fn basic_heap_alloc<H: HeapManager>(mem_type: MemType) {
        let page_cnt = 16;
        let mut heap = H::new(MemAddrRange::from(mem_type) as usize as *mut u8);
        let addr_range = H::mem_addr_range();

        let page_layout = Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap();

        // allocate all pages
        let mut allocated = vec![];
        for _i in 0..page_cnt {
            let ptr = unsafe { heap.alloc_frame(page_layout).unwrap() };
            assert_eq!(ptr as usize % PAGE_SIZE, 0);
            assert_eq!(ptr as usize & addr_range as usize, addr_range as usize);
            allocated.push(ptr);
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
            assert_eq!(ptr as usize % PAGE_SIZE, 0);
            allocated.push(ptr);
        }
    }

    #[test]
    fn dram_heap() {
        basic_heap_alloc::<DRAMHeap>(MemType::DRAM);
    }

    #[test]
    fn pm_heap() {
        basic_heap_alloc::<PMHeap>(MemType::PM);
    }
}
