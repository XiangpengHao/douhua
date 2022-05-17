use std::mem::MaybeUninit;

#[cfg(not(all(feature = "shuttle", test)))]
use std::sync::atomic::AtomicPtr;

#[cfg(all(feature = "shuttle", test))]
use shuttle::sync::atomic::AtomicPtr;

#[derive(Debug)]
pub(crate) struct AtomicListNode {
    pub next: AtomicPtr<AtomicListNode>,
}

impl Default for AtomicListNode {
    fn default() -> Self {
        Self::new()
    }
}

impl AtomicListNode {
    pub(crate) fn new() -> Self {
        unsafe { MaybeUninit::zeroed().assume_init() }
    }

    /// casting a *u8 to *ListNode can be UB because of alignment
    #[allow(clippy::cast_ptr_alignment)]
    pub(crate) fn from_u8_ptr_unchecked(addr: *mut u8) -> *mut AtomicListNode {
        addr as *mut AtomicListNode
    }
}

pub(crate) struct ListNode {
    pub next: Option<&'static mut ListNode>,
}

impl ListNode {
    pub(crate) fn new() -> Self {
        ListNode { next: None }
    }

    pub(crate) fn start_address(&self) -> *const u8 {
        self as *const Self as *const u8
    }

    /// casting a *u8 to *ListNode can be UB because of alignment
    #[allow(clippy::cast_ptr_alignment)]
    pub(crate) fn from_u8_ptr_unchecked(addr: *mut u8) -> *mut ListNode {
        addr as *mut ListNode
    }
}
