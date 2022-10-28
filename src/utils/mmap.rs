use crate::error::SystemError;
use std::ptr;

pub(crate) unsafe fn unmap_memory(addr: *mut u8, size: usize) {
    libc::munmap(addr as *mut libc::c_void, size);
}

pub(crate) struct MmapBuilder {
    heap_size: usize,
    addr: Option<*const u8>,
    fd: Option<i32>,
    flags: i32,
}

impl MmapBuilder {
    pub(crate) fn new(heap_size: usize) -> Self {
        MmapBuilder {
            heap_size,
            addr: None,
            fd: None,
            flags: libc::MAP_HUGE_2MB,
        }
    }

    pub(crate) fn addr(mut self, addr: *const u8) -> Self {
        self.flags |= libc::MAP_FIXED;
        self.addr = Some(addr);
        self
    }

    pub(crate) fn flags(mut self, flags: i32) -> Self {
        self.flags |= flags;
        self
    }

    #[cfg(feature = "pmem")]
    pub(crate) fn huge_page(mut self) -> Self {
        self.flags |= libc::MAP_HUGETLB;
        self
    }

    /// Memory map an nvm-based file
    /// Use `MAP_SHARED_VALIDATE` and `MAP_SYNC` as specified here:
    /// https://man7.org/linux/man-pages/man2/mmap.2.html
    #[cfg(feature = "pmem")]
    pub(crate) fn nvm_file(mut self, fd: i32) -> Self {
        self.flags |= libc::MAP_SYNC | libc::MAP_SHARED_VALIDATE;
        self.fd = Some(fd);
        self
    }

    pub(crate) fn disk_file(mut self, fd: i32) -> Self {
        self.fd = Some(fd);
        self
    }

    pub(crate) fn map(&self) -> Result<*mut u8, SystemError> {
        let mapped_addr: *mut u8 = unsafe {
            libc::mmap(
                self.addr.unwrap_or(ptr::null_mut()) as *mut libc::c_void,
                self.heap_size,
                libc::PROT_WRITE | libc::PROT_READ,
                self.flags,
                self.fd.unwrap_or(-1),
                0,
            ) as *mut u8
        };

        let heap_start = {
            if mapped_addr == libc::MAP_FAILED as *mut u8 {
                return Err(SystemError::MmapFail);
            } else if self.addr.is_some() && mapped_addr as usize != self.addr.unwrap() as usize {
                return Err(SystemError::MmapMismatchAddr);
            } else {
                mapped_addr
            }
        };
        Ok(heap_start)
    }
}

/// A helper to create builder for dram mapping
pub(crate) fn map_dram_builder(
    heap_size: usize,
    addr: Option<*const u8>,
    fd: Option<i32>,
) -> MmapBuilder {
    let mut builder = MmapBuilder::new(heap_size);
    if let Some(fd) = fd {
        builder = builder.disk_file(fd);
    }

    if let Some(addr) = addr {
        builder = builder.addr(addr);
    }

    builder.flags(libc::MAP_ANONYMOUS | libc::MAP_PRIVATE)
}
