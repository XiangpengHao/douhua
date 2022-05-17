pub(crate) mod mmap;

pub(crate) const PM_PAGE_SIZE: usize = 2 * 1024 * 1024; // 2MB

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
}

impl From<MemAddrRange> for MemType {
    fn from(range: MemAddrRange) -> Self {
        match range {
            MemAddrRange::DRAM => MemType::DRAM,
            MemAddrRange::PM => MemType::PM,
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

pub(crate) fn shuttle_yield() {
    #[cfg(all(feature = "shuttle", test))]
    {
        shuttle::thread::yield_now();
    }
}
