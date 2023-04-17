// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
This file describes an experimental extension to linearity support in dafny.
With this extension, linear Dafny programs can declare inout arguments
to functions, which act as unique mutable references.
This extends the ability of programs to express in-place updates of
functional data structures.
*/

module Basic {
  linear datatype LD = LD(i:int)

  // A method argument can be declared as `linear inout` to denote it takes a
  // "mutable borrow", rather than transferring linear ownership.
  method increment(linear inout ld: LD)
  // The state of the argument (`ld` in this case) in the pre-state can be
  // referenced as `old_ld` (both in requires and ensures clauses). The state
  // of the argument in the post-state can be referenced as `ld`.
  ensures ld == old_ld.(i := old_ld.i + 1)
  {
    // The `inout` keyword also marks assignment to fields (or fields-of-fields)
    // of `linear inout` arguments. Assignment is only allowed to an ordinary
    // sub-field of a sequence of linear fields or subfields: more details on
    // this in a more complex example below.
    inout ld.i := ld.i + 1;
  }

  method example() {
    linear var ld := LD(3);
    // Calls to methods with inout arguments must mark the mutable borrow
    // with the `inout` keyword in front of the formal to be borrowed.
    increment(inout ld);
    assert ld.i == 4;
    linear var LD(_) := ld;
  }
}

/* With appropriate TCB support, this enables modifying sequence elements
in place. */

module LinearSequance {
  // Allocate a linear sequence filled with `length` copies of ordinary elements.
  method {:extern} seq_alloc<A>(length: nat, a: A) returns (linear s: seq<A>)
      ensures |s| == length as nat
      ensures forall i: nat | i < |s| :: s[i] == a

  // Deallocate a linear sequence.
  method {:extern} seq_free<A>(linear s: seq<A>)

  // Set an element in the sequence.
  method {:extern} seq_set<A>(linear inout s: seq<A>, i: nat, a: A)
      requires i < |old_s|
      ensures s == old_s[i := a]

  // Get an element from the sequence.
  method {:extern} seq_get<A>(shared s: seq<A>, i: nat) returns (a: A)
      requires i < |s|
      ensures a == s[i]

  method example() {
    linear var xs := seq_alloc(10, 3);
    assert forall j: nat | j < |xs| :: xs[j] == 3;
    seq_set(inout xs, 7, 4);
    assert xs[3] == 3;
    var x := seq_get(xs, 7);
    assert x == 4;
    seq_free(xs);
  }
}

/* Linear datatypes can contain ghost fields. Assignment to such fields
is supported by marking them with `inout ghost`. */
module InoutGhost {
  linear datatype Val0 = Leaf(x:bool, ghost x2:bool)

  predicate Inv(v: Val0) {
    v.x == v.x2
  }

  method flip(linear inout v: Val0)
  requires Inv(old_v)
  ensures v.x2 == !old_v.x2
  ensures Inv(v)
  {
    inout v.x := !v.x;
    // This is necessary to re-establish Inv(v)
    inout ghost v.x2 := v.x;
  }

  method Main() {
    linear var v := Leaf(false, false);
    flip(inout v);
    var b := v.x;
    assert b;
    assert v.x2;
    linear var Leaf(_, _) := v;
  }
}

/* Inout is also supported as a modifier for `this` in datatype members.
Due to a current limitation, linear datatype methods marked `linear inout`
must refer to `old_self` and `self`, rather than `this`, as they ought to. */
module DatatypeMembers {
  linear datatype Val0 = Leaf(x:bool) {
    linear inout method flip_inner()
    ensures self.x == !old_self.x
    {
      inout self.x := !self.x;
    }

    linear inout method flip()
    ensures self.x == !old_self.x
    {
      inout self.flip_inner();
    }
  }

  method example() {
    linear var v := Leaf(true);
    inout v.flip();
    var b := v.x;
    assert !b;
    linear var Leaf(_) := v;
  }
}
