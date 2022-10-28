#![feature(vec_into_raw_parts)]
#![feature(thread_id_value)]

#[cfg(feature = "pmem")]
mod alchemy_alloc;
mod allocator;
mod error;
mod heap;
mod list_node;
mod utils;

use std::{alloc::Layout, ptr::NonNull};

#[cfg(feature = "pmem")]
pub use alchemy_alloc::AlchemyAlloc;
pub use allocator::Allocator;
pub use error::AllocError;
pub use utils::MemType;

/// # Safety
/// Please check the official documentation of [`std::alloc::Allocator`](https://doc.rust-lang.org/std/alloc/trait.Allocator.html)
pub unsafe trait TieredAllocator {
    fn allocate(&self, layout: Layout, mem_type: MemType) -> Result<NonNull<[u8]>, AllocError>;

    /// # Safety
    /// Please check the official documentation of [`std::alloc::Allocator`](https://doc.rust-lang.org/std/alloc/trait.Allocator.html)
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout, mem_type: MemType);

    fn allocate_zeroed(
        &self,
        layout: Layout,
        mem_type: MemType,
    ) -> Result<NonNull<[u8]>, AllocError> {
        let mut ptr = self.allocate(layout, mem_type)?;
        // SAFETY: `alloc` returns a valid memory block
        unsafe { ptr.as_mut().as_mut_ptr().write_bytes(0, ptr.len()) }
        Ok(ptr)
    }
}
