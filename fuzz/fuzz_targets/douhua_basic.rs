#![no_main]
use std::{alloc::Layout, collections::HashMap};

use arbitrary::Arbitrary;
use douhua::Allocator;
use libfuzzer_sys::fuzz_target;

/// Follow the tutorial from this post: https://tiemoko.com/blog/diff-fuzz/
#[derive(Arbitrary, Debug)]
enum MapMethod {
    Alloc { size: u8 },
    Dealloc { id: i32 },
}

fuzz_target!(|methods: Vec<MapMethod>| {
    let mut allocated = HashMap::new();
    let mut alloc_cnt = 0;

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
                allocated.insert(alloc_cnt, (ptr, size));
                alloc_cnt += 1;
            }
            MapMethod::Dealloc { id } => {
                let to_dealloc = allocated.get(&(id as usize));
                if let Some((ptr, size)) = to_dealloc {
                    unsafe {
                        for j in 0..*size {
                            assert_eq!(*ptr.add(j as usize), *size);
                        }
                    }
                    let layout = Layout::from_size_align(*size as usize * 8, 1).unwrap();
                    unsafe { Allocator::get().dealloc(*ptr, layout) };
                    allocated.remove(&(id as usize));
                }
            }
        }
    }

    for (_key, (ptr, size)) in allocated.into_iter() {
        unsafe {
            for j in 0..size {
                assert_eq!(*ptr.add(j as usize), size);
            }
        }
        let layout = Layout::from_size_align(size as usize * 8, 1).unwrap();
        unsafe { Allocator::get().dealloc(ptr, layout) };
    }
});
