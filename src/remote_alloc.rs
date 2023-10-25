use std::{
    alloc::{Allocator, Layout},
    ptr::NonNull,
};

use crate::{allocator::AllocInner, heap::shm::ShmHeap};

pub struct RemoteAlloc {
    inner: AllocInner<ShmHeap>,
}

impl RemoteAlloc {
    pub fn new() -> Self {
        let inner = AllocInner::<ShmHeap>::new();
        Self { inner }
    }
}

unsafe impl Allocator for RemoteAlloc {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, std::alloc::AllocError> {
        let ptr = self.allocate(layout).map_err(|_e| std::alloc::AllocError)?;
        Ok(ptr)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        self.dealloc(ptr, layout);
    }
}

impl RemoteAlloc {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, crate::AllocError> {
        let ptr = self.inner.safe_alloc(layout)?;
        let ptr_slice = std::ptr::slice_from_raw_parts_mut(ptr, layout.size());
        Ok(std::ptr::NonNull::new(ptr_slice).unwrap())
    }

    fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        self.inner.dealloc_inner(ptr.as_ptr(), layout)
    }
}

#[cfg(test)]

mod tests {
    use super::*;

    #[test]
    fn test_hashmap() {
        let allocator = RemoteAlloc::new();
        let mut ht = hashbrown::HashMap::new_in(&allocator);
        for i in 0..1000_000 {
            ht.insert(i, i);
        }

        for i in 0..1000_000 {
            assert_eq!(ht.get(&i), Some(&i));
        }
    }
}
