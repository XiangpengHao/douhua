#![feature(slice_ptr_get)]

use std::alloc::Layout;

use douhua::{Allocator, TieredAllocator};

const PM_PAGE_SIZE: usize = 1024 * 1024 * 2;

#[test]
fn basic() {
    let alloc_layout = Layout::from_size_align(64, 64).unwrap();
    let max_cnt = PM_PAGE_SIZE / alloc_layout.size();

    let mut allocated = vec![];

    // allocate all memory, the layout are aligned so we can use all the memory
    for i in 0..max_cnt {
        let mut ptr = Allocator::get()
            .allocate_zeroed(alloc_layout, douhua::MemType::DRAM)
            .unwrap();
        let val = unsafe { ptr.as_mut() };
        for j in 0..alloc_layout.size() {
            val[j] = i as u8;
        }
        allocated.push(ptr);
    }

    // check sanity and dealloc them
    for (i, ptr) in allocated.into_iter().enumerate() {
        let val = unsafe { ptr.as_ref() };
        for j in 0..alloc_layout.size() {
            assert_eq!(val[j], i as u8);
        }

        unsafe {
            Allocator::get().deallocate(ptr.as_non_null_ptr(), alloc_layout, douhua::MemType::DRAM);
        }
    }
}
