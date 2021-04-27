#![allow(dead_code)]

use std::sync::atomic::{AtomicU32, AtomicBool, Ordering};
use std::cell::UnsafeCell;

struct RWLock<T> {
  cell: UnsafeCell<T>,
  exc: AtomicBool,
  rc: AtomicU32,
}

impl<T> RWLock<T> {
  pub fn new(t: T) -> RWLock<T> {
    return RWLock{
      cell: UnsafeCell::new(t),
      exc: AtomicBool::new(false),
      rc: AtomicU32::new(0),
    };
  }

  pub fn acquire_exclusive(&self, fun: fn(&mut T) -> ()) {
    loop {
      let res = self.exc.compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst);
      if res.is_ok() {
        break;
      }
    }

    loop {
      let r = self.rc.load(Ordering::SeqCst);
      if r == 0 {
        break;
      }
    }

    let mut borrow;
    unsafe {
      borrow = &mut *self.cell.get();
    }

    fun(&mut borrow);

    self.exc.store(false, Ordering::SeqCst);
  }

  pub fn acquire_shared(&self, fun: fn(& T) -> ()) {
    loop {
      loop {
        let r = self.exc.load(Ordering::Relaxed);
        if !r { break; }
      }

      self.rc.fetch_add(1, Ordering::SeqCst);

      let already_taken = self.exc.load(Ordering::SeqCst);

      if !already_taken {
        break;
      } else {
        self.rc.fetch_sub(1, Ordering::SeqCst);
      }
    }

    let borrow;
    unsafe {
      borrow = & *self.cell.get();
    }

    fun(borrow);

    self.rc.fetch_sub(1, Ordering::SeqCst);
  }
}

fn main() {
}
