use std::alloc::Layout;

use crate::{
    error::AllocError,
    list_node::ListNode,
    utils::{
        mmap::{map_dram_builder, unmap_memory},
        PAGE_SIZE,
    },
    MemType,
};

use super::{align_up, HeapManager, InnerHeap, MemAddrRange};

pub struct DRAMHeap {
    inner_heap: InnerHeap,
    virtual_high_addr: *mut u8,
}

unsafe impl Send for DRAMHeap {}
unsafe impl Sync for DRAMHeap {}

const DRAM_DEFAULT_ALLOC_SIZE: usize = 1024 * 1024 * 512; // 512MB

impl HeapManager for DRAMHeap {
    fn new(heap_start_addr: *mut u8) -> Self {
        let heap_start_addr =
            DRAMHeap::map_dram_pool(DRAM_DEFAULT_ALLOC_SIZE, Some(heap_start_addr as *const u8))
                .expect("failed to create DRAM heap pool!");

        let inner_heap = InnerHeap {
            heap_size: DRAM_DEFAULT_ALLOC_SIZE,
            heap_start: heap_start_addr,
            next_alloc_addr: heap_start_addr,
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
            self.alloc_page()
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
    fn alloc_page(&mut self) -> Result<*mut u8, AllocError> {
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
                    self.alloc_page()
                }
            }
        }
    }
}
