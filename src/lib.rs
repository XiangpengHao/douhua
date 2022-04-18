#![feature(vec_into_raw_parts)]
#![feature(thread_id_value)]

mod allocator;
mod error;
mod heap;
mod list_node;
mod obj_alloc;
mod utils;

const PM_PAGE_SIZE: usize = 2 * 1024 * 1024; // 2MB

extern "C" {
    fn __asan_unpoison_memory_region(addr: *const u8, size: usize);
    fn __asan_poison_memory_region(addr: *const u8, size: usize);
}

pub(crate) fn poison_memory_region(addr: *const u8, size: usize) {
    if cfg!(feature = "sans") {
        unsafe {
            __asan_poison_memory_region(addr, size);
        }
    }
}

pub(crate) fn unpoison_memory_region(addr: *const u8, size: usize) {
    if cfg!(feature = "sans") {
        unsafe {
            __asan_unpoison_memory_region(addr, size);
        }
    }
}
