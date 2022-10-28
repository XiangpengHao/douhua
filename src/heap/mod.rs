use crate::{
    error::AllocError,
    utils::{MemType, PAGE_SIZE},
};

use super::list_node::ListNode;
use std::alloc::Layout;

pub(crate) mod dram;

#[cfg(feature = "numa")]
pub(crate) mod numa;

#[cfg(feature = "pmem")]
pub(crate) mod pm;

/// To deallocate the memory we need a way to tell the memory type,
/// i.e. we need to know where it comes from, {local, remote} {DRAM PM}
/// The easiest way is to partition the virtual memory address.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
#[allow(clippy::upper_case_acronyms)]
#[allow(clippy::enum_clike_unportable_variant)]
pub(crate) enum MemAddrRange {
    DRAM = 0x5a00_0000_0000,
    #[cfg(feature = "pmem")]
    PM = 0x5d00_0000_0000,
    #[cfg(feature = "numa")]
    NUMA = 0, // numa memory don't have a fixed address range
}

impl From<MemType> for MemAddrRange {
    fn from(t: MemType) -> Self {
        match t {
            #[cfg(feature = "pmem")]
            MemType::PM => MemAddrRange::PM,
            MemType::DRAM => MemAddrRange::DRAM,
            #[cfg(feature = "numa")]
            MemType::NUMA => MemAddrRange::NUMA,
        }
    }
}

impl From<*const u8> for MemAddrRange {
    fn from(addr: *const u8) -> Self {
        let dram_range = MemAddrRange::DRAM as usize;
        if (addr as usize & dram_range) == dram_range {
            return MemAddrRange::DRAM;
        }

        #[cfg(feature = "pmem")]
        {
            let pm_range = MemAddrRange::PM as usize;
            if (addr as usize & pm_range) == pm_range {
                return MemAddrRange::PM;
            }
        }

        #[cfg(feature = "numa")]
        return MemAddrRange::NUMA;

        #[cfg(all(not(feature = "pmem"), not(feature = "numa")))]
        unreachable!()
    }
}

/// This struct manages all the small memory allocation (2MB pages)
struct InnerHeap {
    heap_start: *mut u8,
    heap_size: usize,
    free_list: ListNode,
    next_alloc_addr: *mut u8,
}

impl InnerHeap {
    fn expand_free_page(&mut self) -> Result<*mut u8, AllocError> {
        let page_start = self.next_alloc_addr;
        if page_start as *const u8 == self.heap_end() {
            return Err(AllocError::OutOfMemory);
        }
        self.next_alloc_addr = unsafe { self.next_alloc_addr.add(PAGE_SIZE) };
        Ok(page_start as *mut u8)
    }

    fn heap_end(&self) -> *const u8 {
        unsafe { self.heap_start.add(self.heap_size) }
    }

    /// Add a 2MB page to the temporary free list
    fn add_free_page(&mut self, addr: *mut u8) {
        let mut node = ListNode::new();
        node.next = self.free_list.next.take();

        let node_ptr = ListNode::from_u8_ptr_unchecked(addr);
        unsafe { node_ptr.write(node) };
        self.free_list.next = Some(unsafe { &mut *node_ptr });
    }
}

pub(crate) trait HeapManager: Send + Sync {
    fn new(heap_start_addr: *mut u8) -> Self;

    /// # Safety
    /// Allocates frame using mmap is unsafe
    unsafe fn alloc_frame(&mut self, layout: Layout) -> Result<*mut u8, AllocError>;

    /// # Safety
    /// Deallocate memory is unsafe
    unsafe fn dealloc_frame(&mut self, ptr: *mut u8, layout: Layout);

    fn mem_addr_range() -> MemAddrRange;
}

/// Align the given address `size` upwards to alignment `align`.
///
/// Requires that `align` is a power of two.
fn align_up(size: usize, align: usize) -> usize {
    (size + align - 1) & !(align - 1)
}

#[cfg(test)]
mod tests {
    use crate::utils::PAGE_SIZE;

    use super::*;
    use std::alloc::Layout;

    fn basic_heap_alloc<H: HeapManager>(mem_type: MemType) {
        let page_cnt = 16;
        let mut heap = H::new(MemAddrRange::from(mem_type) as usize as *mut u8);
        let addr_range = H::mem_addr_range();

        let page_layout = Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap();

        // allocate all pages
        let mut allocated = vec![];
        for _i in 0..page_cnt {
            let ptr = unsafe { heap.alloc_frame(page_layout).unwrap() };
            assert_eq!(ptr as usize % PAGE_SIZE, 0);
            assert_eq!(ptr as usize & addr_range as usize, addr_range as usize);
            allocated.push(ptr);
        }

        // deallocate them
        for ptr in allocated {
            unsafe {
                heap.dealloc_frame(ptr, page_layout);
            }
        }

        // can allocate again
        let mut allocated = vec![];
        for _i in 0..page_cnt {
            let ptr = unsafe { heap.alloc_frame(page_layout).unwrap() };
            assert_eq!(ptr as usize % PAGE_SIZE, 0);
            allocated.push(ptr);
        }
    }

    #[test]
    fn dram_heap() {
        basic_heap_alloc::<dram::DRAMHeap>(MemType::DRAM);
    }

    #[cfg(feature = "pmem")]
    #[test]
    fn pm_heap() {
        basic_heap_alloc::<pm::PMHeap>(MemType::PM);
    }
}
