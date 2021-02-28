// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use std::cell::RefCell;
use std::rc::Rc;

// encapsulated interior mutability

struct Datum {
    val: u64,
}

struct StructA {
    val: Rc<RegionA, RefCell<Datum>>,
    left: Option<Box<StructA>>,
    right: Option<Box<StructB>>,
}

struct StructB {
    val: Rc<RegionA, RefCell<Datum>>,
    left: Option<Box<StructA>>,
    right: Option<Box<StructB>>,
}

fn main() {

    let a = Rc::new(RefCell::new(Object::new())); 
    assert something_is_true(a);
    let b = a.clone();
    assert something_is_true(b);

    do_something("REALLY shared" a); // immutable bit

    assert something_is_true(b); // not true anymore!!!




    // unsafe {
    //     let aref = &mut a;
    //     let aptr = aref as *mut Object; // raw pointer, untracked by borrow checker
    //     let b = aptr as &mut Object;
    //     let c = aptr as &mut Object; // undefined behaviour
    // }
}
