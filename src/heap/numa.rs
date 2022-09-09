use std::alloc::Layout;

use crate::{error::AllocError, list_node::ListNode, utils::PAGE_SIZE};

use super::{align_up, HeapManager, InnerHeap};

pub struct NumaHeap {
    inner_heap: InnerHeap,
    virtual_high_addr: *mut u8,
}

unsafe impl Send for NumaHeap {}
unsafe impl Sync for NumaHeap {}

const FAR_NODE: i32 = 1;
const NUMA_DEFAULT_ALLOC_SIZE: usize = 1024 * 1024 * 512; // 512MB

impl HeapManager for NumaHeap {
    fn new(_heap_start_addr: *mut u8) -> Self {
        #[cfg(not(feature = "mock_numa"))]
        {
            unsafe {
                let v = libnuma_sys::numa_available();
                assert!(v != -1, "numa is not available on this machine.");
            }
        }
        let heap_start_addr = NumaHeap::alloc_mem_onnode(FAR_NODE, NUMA_DEFAULT_ALLOC_SIZE);

        let inner_heap = InnerHeap {
            heap_size: NUMA_DEFAULT_ALLOC_SIZE,
            heap_start: heap_start_addr,
            high_addr: heap_start_addr,
            free_list: ListNode::new(),
        };

        NumaHeap {
            inner_heap,
            virtual_high_addr: unsafe { heap_start_addr.add(NUMA_DEFAULT_ALLOC_SIZE) },
        }
    }

    unsafe fn alloc_frame(&mut self, layout: Layout) -> Result<*mut u8, AllocError> {
        let size = layout.size();
        if size <= PAGE_SIZE {
            self.alloc_page(layout)
        } else {
            self.alloc_large(layout)
        }
    }

    unsafe fn dealloc_frame(&mut self, ptr: *mut u8, layout: Layout) {
        let aligned_size = align_up(layout.size(), PAGE_SIZE);
        if cfg!(feature = "mock_numa") {
            std::alloc::dealloc(ptr, layout);
        } else {
            unsafe {
                libnuma_sys::numa_free(ptr as *mut libc::c_void, aligned_size);
            }
        }
    }

    fn mem_addr_range() -> super::MemAddrRange {
        super::MemAddrRange::NUMA
    }
}

impl NumaHeap {
    fn alloc_mem_onnode(node: i32, size_byte: usize) -> *mut u8 {
        // FIXME: actually do the aligned allocation.
        if cfg!(feature = "mock_numa") {
            let layout = std::alloc::Layout::from_size_align(size_byte, PAGE_SIZE).unwrap();
            unsafe { std::alloc::alloc(layout) }
        } else {
            let ptr = unsafe { libnuma_sys::numa_alloc_onnode(size_byte, node) as *mut u8 };
            let aligned_ptr = align_up(ptr as usize, PAGE_SIZE);
            aligned_ptr as *mut u8
        }
    }

    fn alloc_large(&mut self, layout: Layout) -> Result<*mut u8, AllocError> {
        let aligned_size = align_up(layout.size(), PAGE_SIZE);
        self.virtual_high_addr = unsafe { self.virtual_high_addr.add(aligned_size) };
        Ok(Self::alloc_mem_onnode(FAR_NODE, aligned_size))
    }

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
                        Layout::from_size_align(NUMA_DEFAULT_ALLOC_SIZE, PAGE_SIZE).unwrap(),
                    )?;
                    self.inner_heap.heap_size += NUMA_DEFAULT_ALLOC_SIZE;
                    self.alloc_page(layout)
                }
            }
        }
    }
}
