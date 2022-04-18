use thiserror::Error;

/// Internal unrecoverable system error
#[derive(Debug, Error)]
pub(crate) enum SystemError {
    #[error("failed to allocate pm file")]
    FileAlloc,
    #[error("failed to mmap the pm file")]
    MmapFail,
    #[error("mmap mapped to a different address")]
    MmapMismatchAddr,
    #[error("Allocator run out of memory")]
    ArrayAllocatorOutOfMemory,
}

#[derive(Debug, Error)]
pub enum AllocError {
    #[error("unknown error")]
    Unknown,
    #[error("out of memory")]
    OutOfMemory,
    #[error("failed to alloc file")]
    FileAlloc,
    #[error("internal error from mmap")]
    MmapFail,
    #[error("mmap did not map to the expected address")]
    MmapMismatchAddr,
    #[error("invalid memory address")]
    InvalidAddr,
}
