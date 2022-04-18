use std::sync::atomic::{AtomicU64, Ordering};

pub(crate) mod mmap;

thread_local! {
    static TID: AtomicU64 = AtomicU64::new(0);
}

pub fn get_tid() -> u64 {
    TID.with(|t| {
        let old = t.load(Ordering::Relaxed);
        if old == 0 {
            let new_tid = std::thread::current().id().as_u64().get();
            t.store(new_tid, Ordering::Relaxed);
            new_tid
        } else {
            old
        }
    })
}
