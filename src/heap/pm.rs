use std::{
    alloc::Layout,
    collections::HashMap,
    path::{Path, PathBuf},
};

use crate::{
    error::AllocError,
    list_node::ListNode,
    utils::{
        mmap::{create_and_map_pool, unmap_memory},
        PAGE_SIZE,
    },
    MemType,
};

use super::{align_up, HeapManager, InnerHeap, MemAddrRange};

pub struct PMHeap {
    inner_heap: InnerHeap,
    /// High address in current virtual memory partition
    virtual_high_addr: *mut u8,
    files: HashMap<*mut u8, PathBuf>,
}

unsafe impl Send for PMHeap {}
unsafe impl Sync for PMHeap {}

const PM_DEFAULT_ALLOC_SIZE: usize = 1024 * 1024 * 512; // 1GB

impl HeapManager for PMHeap {
    fn new(heap_start_addr: *mut u8) -> Self {
        // lazy init the frame, no allocation on creation.
        PMHeap {
            inner_heap: InnerHeap {
                heap_size: 0,
                high_addr: heap_start_addr,
                free_list: ListNode::new(),
                heap_start: heap_start_addr,
            },
            virtual_high_addr: heap_start_addr,
            files: HashMap::new(),
        }
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
        unsafe {
            // pre-fault the pages
            std::ptr::write_bytes(rv.0, 1, rv.1);
        }
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
