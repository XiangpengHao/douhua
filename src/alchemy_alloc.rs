use std::{
    alloc::Layout,
    sync::{
        atomic::{AtomicPtr, Ordering},
        Mutex,
    },
};

use once_cell::sync::OnceCell;

use crate::{
    error::AllocError,
    heap::{pm::PMHeap, HeapManager, MemAddrRange},
    utils::{backoff::Backoff, PAGE_SIZE},
};

#[cfg(feature = "shard-6")]
const SHARD_NUM: usize = 8;

#[cfg(not(feature = "shard-6"))]
const SHARD_NUM: usize = 1;

static ALLOCATOR: once_cell::sync::OnceCell<[AlchemyAlloc; SHARD_NUM]> = OnceCell::new();

/// A pm-only alloc-only allocator
pub struct AlchemyAlloc {
    block: AtomicPtr<u8>,
    heap_manager: Mutex<PMHeap>,
}

impl AlchemyAlloc {
    pub fn get() -> &'static AlchemyAlloc {
        let allocators = ALLOCATOR.get_or_init(|| {
            let mem_each_shard =
                (MemAddrRange::PM as usize - MemAddrRange::DRAM as usize) / SHARD_NUM;
            let mut allocators: [std::mem::MaybeUninit<AlchemyAlloc>; SHARD_NUM] =
                unsafe { std::mem::MaybeUninit::uninit().assume_init() };

            for (i, elem) in allocators.iter_mut().enumerate() {
                let heap_start = MemAddrRange::PM as usize + i * mem_each_shard;
                unsafe {
                    std::ptr::write(elem.as_mut_ptr(), AlchemyAlloc::new(heap_start as *mut u8));
                }
            }
            unsafe { std::mem::transmute::<_, [AlchemyAlloc; SHARD_NUM]>(allocators) }
        });

        #[cfg(feature = "shard-6")]
        {
            use nanorand::Rng;
            let v = nanorand::tls_rng().generate_range(0..SHARD_NUM);
            unsafe { allocators.get_unchecked(v) }
        }

        #[cfg(not(feature = "shard-6"))]
        {
            &allocators[0]
        }
    }

    fn new(heap_start_addr: *mut u8) -> Self {
        Self {
            block: Default::default(),
            heap_manager: Mutex::new(PMHeap::new(heap_start_addr)),
        }
    }

    /// # Safety
    /// Internal use
    pub unsafe fn alloc_pm(&self, layout: Layout) -> Result<*mut u8, AllocError> {
        if layout.size() > PAGE_SIZE {
            panic!("Allocator only supports allocation of size <= 2MB");
        }

        let backoff = Backoff::new();

        loop {
            // the order matters, addr must load before allocated
            let ptr = self.block.load(Ordering::Acquire);

            if ptr as usize == usize::MAX {
                // someone is holding the lock, wait for a new page
                backoff.spin();
                continue;
            }

            if ((ptr as usize & 0x1f_ffff) + layout.size() > (PAGE_SIZE - 1)) || ptr.is_null() {
                // too large, we should move to a new page
                if let Err(_v) = self.block.compare_exchange_weak(
                    ptr,
                    usize::MAX as *mut u8,
                    Ordering::Acquire,
                    Ordering::Acquire,
                ) {
                    backoff.spin();
                }

                // we got the lock, we can allocate a new page
                let page_layout = Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap();
                let mut heap_manager = if let Ok(h) = self.heap_manager.lock() {
                    h
                } else {
                    self.block.store(ptr, Ordering::Release);
                    backoff.spin();
                    continue;
                };
                let page_mem = match { heap_manager.alloc_frame(page_layout) } {
                    Ok(v) => v,
                    Err(v) => {
                        self.block.store(ptr, Ordering::Release);
                        return Err(v);
                    }
                };

                self.block
                    .store(page_mem.add(layout.size()), Ordering::Release);
                return Ok(page_mem);
            } else {
                let new_ptr = ptr.add(layout.size());
                match self.block.compare_exchange_weak(
                    ptr,
                    new_ptr,
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return Ok(ptr),
                    Err(_) => backoff.spin(),
                }
            }
        }
    }

    /// # Safety
    /// Internal use
    pub unsafe fn alloc_pm_zeroed(&self, layout: Layout) -> Result<*mut u8, AllocError> {
        let ptr = self.alloc_pm(layout)?;
        std::ptr::write_bytes(ptr, 0, layout.size());
        Ok(ptr)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{heap::MemAddrRange, AlchemyAlloc};

    #[test]
    fn basic() {
        let allocator = AlchemyAlloc::new(MemAddrRange::PM as usize as *mut u8);

        let layout = Layout::from_size_align(128, 128).unwrap();

        let alloc_cnt = 1024;

        let mut allocated = vec![];
        for _i in 0..alloc_cnt {
            let ptr = unsafe { allocator.alloc_pm_zeroed(layout).unwrap() };
            for i in 0..128 {
                unsafe {
                    *ptr.add(i) = i as u8;
                }
            }
            allocated.push(ptr);
        }

        for i in allocated.iter() {
            for j in 0..128 {
                unsafe {
                    assert_eq!(*i.add(j), j as u8);
                }
            }
        }
    }
}
