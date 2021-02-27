// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT


module Cow {
  type {:extern "predefined"} cow<A>

  function cow_content<A>(self: cow<A>): A

  static method {:extern} cow_alloc<A>(linear a: A, /*do what LinearBox does*/ cloner:(linear A)->(linear A, linear A)) returns (linear cow: cow<A>)
  ensures cow_content(cow) == a

  method {:extern} cow_clone<A>(shared self: cow<A>) returns (linear cloned: cow<A>)
  ensures cow_content(cloned) == cow_content(self)

  method {:extern} cow_borrow<A>(shared self: cow<A>) returns (shared borrowed: A)
  ensures borrowed == cow_content(self)

  method {:extern} cow_unwrap<A>(linear self: cow<A>) returns (linear taken: A)
  ensures taken == cow_content(self)

  // decrements the reference count
  method {:extern} cow_free<A>(linear self: cow<A>)
}

module User {
  import Cow

  linear datatype Thing = Thing(a: nat)

  // method Illegal() {
  //   linear var t := Thing(12);
  //   linear var cowt := Cow.cow_alloc(t);
  //   linear var Cow(flag) := cowt;
      // --> Error: to use a pattern, the type of the source/RHS expression must be a datatype (instead found ?)
  // }

  function method CloneThing(linear t: Thing) : (linear Thing, linear Thing) {
    linear var t1 := Thing(t.a);
    linear var t2 := t;
    (t1, t2)
  }

  method AllocDealloc() {
    linear var t := Thing(12);
    linear var cowt := Cow.cow_alloc(t, CloneThing);
    Cow.cow_free(cowt);
  }
}








// linear datatype Sector = SomeSector(linear block: Cow<Block>)
// linear datatype Block = Block(a: u64)
// 
// linear var b := Block(14);
//
// linear var cowb := Cow.Alloc(b);
//
// cache.Insert(cowb);
//
// ---
//
// linear var cowb: Cow<Block> := cache.Get(somekey).Clone();
//
// linear var sec := SomeSector(cowb);
//
// linear var SomeSector(cowb) := sec;
// 
// cowb.Free(); // correct
// linear var Cow() := cowb; // broken (leak risk)
//
// --
//
// linear var b: Block := cache.Take(somekey).Unwrap();
//
// inout b.somefield := 23;
//
// linear var cowb := Cow.Alloc(b);
//
// cache.Insert(somekey, cowb);
//
