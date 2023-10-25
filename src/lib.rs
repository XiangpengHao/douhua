#![feature(vec_into_raw_parts)]
#![feature(thread_id_value)]
#![feature(allocator_api)]

#[cfg(feature = "pmem")]
mod alchemy_alloc;
mod allocator;
mod error;
mod heap;
mod list_node;
mod remote_alloc;
mod utils;

use std::{alloc::Layout, ptr::NonNull};

#[cfg(feature = "pmem")]
pub use alchemy_alloc::AlchemyAlloc;
pub use allocator::Allocator;
pub use error::AllocError;
pub use remote_alloc::RemoteAlloc;
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

#[inline]
#[allow(unused_variables)]
pub fn remote_delay() {
    #[cfg(feature = "add_delay")]
    {
        for _ in 0..(1 << 7) {
            std::hint::spin_loop();
        }
    }
}
