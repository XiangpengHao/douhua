#![no_main]
use std::{alloc::Layout, collections::VecDeque};

use arbitrary::Arbitrary;
use douhua::Allocator;
use libfuzzer_sys::fuzz_target;

/// Follow the tutorial from this post: https://tiemoko.com/blog/diff-fuzz/
#[derive(Arbitrary, Debug)]
enum MapMethod {
    Alloc { size: u8 },
    Dealloc,
}

fuzz_target!(|methods: Vec<MapMethod>| {
    // fuzzed code goes here
    let mut allocated = VecDeque::new();

    for m in methods {
        match m {
            MapMethod::Alloc { size } => {
                let alloc_layout = Layout::from_size_align(size as usize * 8, 1).unwrap();
                let ptr =
                    unsafe { Allocator::get().alloc_zeroed(alloc_layout, douhua::MemType::DRAM) }
                        .unwrap();
                unsafe {
                    for j in 0..alloc_layout.size() {
                        ptr.add(j).write(size);
                    }
                }
                allocated.push_back((ptr, size));
            }
            MapMethod::Dealloc => {
                if let Some((ptr, size)) = allocated.pop_front() {
                    unsafe {
                        for j in 0..size {
                            assert_eq!(*ptr.add(j as usize), size);
                        }
                    }
                    let layout = Layout::from_size_align(size as usize * 8, 1).unwrap();
                    unsafe { Allocator::get().dealloc(ptr, layout) };
                }
            }
        }
    }

    for (ptr, size) in allocated {
        unsafe {
            for j in 0..size {
                assert_eq!(*ptr.add(j as usize), size);
            }
        }
        let layout = Layout::from_size_align(size as usize * 8, 1).unwrap();
        unsafe { Allocator::get().dealloc(ptr, layout) };
    }
});
