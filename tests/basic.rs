use std::alloc::Layout;

use douhua::Allocator;

const PM_PAGE_SIZE: usize = 1024 * 1024 * 2;

#[test]
fn basic() {
    unsafe {
        Allocator::initialize(1);
    }
    let alloc_layout = Layout::from_size_align(64, 64).unwrap();
    let max_cnt = PM_PAGE_SIZE / alloc_layout.size();

    let mut allocated = vec![];

    // allocate all memory, the layout are aligned so we can use all the memory
    for i in 0..max_cnt {
        let ptr =
            unsafe { Allocator::get().alloc_zeroed(alloc_layout, douhua::MemType::DRAM) }.unwrap();
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

        unsafe {
            Allocator::get().dealloc(ptr, alloc_layout);
        }
    }
}
