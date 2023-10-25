use std::{alloc::Layout, ffi::CString, ptr::null_mut, sync::Mutex};

use crate::{allocator::AllocInner, list_node::ListNode, utils::PAGE_SIZE, AllocError};

use super::{HeapManager, InnerHeap};

pub struct ShmHeap {
    inner_heap: InnerHeap,
}

unsafe impl Send for ShmHeap {}
unsafe impl Sync for ShmHeap {}

const SHM_DEFAULT_ALLOC_SIZE: usize = 1024 * 1024 * 512; // 512MB

impl HeapManager for ShmHeap {
    fn new(_heap_start_addr: *mut u8) -> Self {
        let identifier = "/shm_heap";
        let shm_name = CString::new(identifier).unwrap();
        let raw_fd = unsafe {
            libc::shm_open(
                shm_name.as_ptr(),
                libc::O_CREAT | libc::O_RDWR,
                libc::S_IRUSR | libc::S_IWUSR,
            )
        };
        if raw_fd < 0 {
            panic!("Failed to create shared memory");
        }

        // Set the size of the shared memory object.
        if unsafe { libc::ftruncate(raw_fd, SHM_DEFAULT_ALLOC_SIZE as _) } < 0 {
            panic!("Failed to set shared memory size");
        }

        let heap_start_addr = unsafe {
            libc::mmap(
                null_mut(),
                SHM_DEFAULT_ALLOC_SIZE,
                libc::PROT_WRITE,
                libc::MAP_SHARED,
                raw_fd,
                0,
            )
        };

        if heap_start_addr == libc::MAP_FAILED {
            panic!("Failed to mmap shared memory");
        }
        let heap_start_addr = heap_start_addr as *mut u8;

        let inner_heap = InnerHeap {
            heap_size: SHM_DEFAULT_ALLOC_SIZE,
            heap_start: heap_start_addr,
            next_alloc_addr: heap_start_addr,
            free_list: ListNode::new(),
        };

        ShmHeap { inner_heap }
    }

    unsafe fn alloc_frame(&mut self, layout: Layout) -> Result<*mut u8, AllocError> {
        if layout.size() > PAGE_SIZE {
            return self.inner_heap.expand_any_size(layout.size());
        }

        if let Some(head_next) = self.inner_heap.free_list.next.take() {
            self.inner_heap.free_list.next = head_next.next.take();
            Ok(head_next.start_address() as *mut u8)
        } else {
            match self.inner_heap.expand_free_page() {
                Ok(addr) => Ok(addr),
                Err(e) => {
                    assert!(matches!(e, AllocError::OutOfMemory));
                    return Err(e);
                }
            }
        }
    }

    unsafe fn dealloc_frame(&mut self, ptr: *mut u8, _layout: Layout) {
        // check ptr is in range
        assert!(ptr >= self.inner_heap.heap_start);
        assert!(ptr <= self.inner_heap.heap_start.add(self.inner_heap.heap_size));
        self.inner_heap.add_free_page(ptr);
    }

    fn mem_addr_range() -> super::MemAddrRange {
        super::MemAddrRange::DRAM
    }
}

impl AllocInner<ShmHeap> {
    pub(crate) fn new() -> Self {
        AllocInner {
            list_heads: Default::default(),
            heap_manager: Mutex::new(ShmHeap::new(0 as usize as *mut u8)),
        }
    }
}
