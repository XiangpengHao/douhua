pub(crate) mod backoff;
pub(crate) mod mmap;

pub(crate) const PAGE_SIZE: usize = 2 * 1024 * 1024; // 2MB

use std::alloc::Layout;

use crate::heap::MemAddrRange;

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

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[allow(clippy::upper_case_acronyms)]
pub enum MemType {
    DRAM,
    PM,
    NUMA,
}

impl From<MemAddrRange> for MemType {
    fn from(range: MemAddrRange) -> Self {
        match range {
            MemAddrRange::DRAM => MemType::DRAM,
            MemAddrRange::PM => MemType::PM,
            MemAddrRange::NUMA => MemType::NUMA,
        }
    }
}

/// This is api a bit controversial, I don't think the caller should rely on the allocator to differentiate the memory location.
/// Instead the caller should track from where they allocate memory.
/// I keep this around just for fast prototyping, it is not a required api.
impl From<*const u8> for MemType {
    fn from(addr: *const u8) -> Self {
        let range = MemAddrRange::from(addr);
        MemType::from(range)
    }
}

/// Block size to use
///
/// The sizes must be power of two because they are also used for block alignment
/// We allow up to 2MB blocks (PM_PAGE_SIZE)
pub(crate) const BLOCK_SIZES: &[usize] = &[
    8,
    16,
    32,
    64,
    128,
    256,
    512,
    1024,
    2048,
    4096,
    4096 * 2,
    4096 * 4,
    4096 * 8,
    4096 * 16,
    4096 * 32,
    4096 * 64,
    4096 * 128,
    4096 * 256,
    4096 * 512,
];

pub(crate) fn list_index(layout: &Layout) -> Option<usize> {
    let required_block_size = layout.size().max(layout.align());

    // This is not the most efficient way, we might want to optimize it if necessary
    BLOCK_SIZES.iter().position(|&s| s >= required_block_size)
}
