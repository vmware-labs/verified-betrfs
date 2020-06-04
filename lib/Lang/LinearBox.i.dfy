include "LinearBox.s.dfy"
include "LinearMaybe.s.dfy"
include "../Base/LinearOption.i.dfy"

module LinearBox {
  import opened LinearBox_s
  import opened LinearMaybe
  import opened LinearOption

  // Warning: does not automatically deallocate the linear value.
  // (either Take and deallocate manually, or use BoxedLinearOption, below, to guarantee deallocation)
  class BoxedLinear<A>
  {
    var data:SwapAffine<maybe<A>>
    ghost var Repr:set<object>

    predicate Inv()
      reads this, Repr
    {
      Repr == {this, this.data}
    }

    function Has():bool
      requires Inv()
      reads this, Repr
    {
      has(data.Read())
    }

    function Read():A
      requires Inv()
      reads this, Repr
    {
      read(data.Read())
    }

    constructor Empty()
      ensures Inv()
      ensures !Has()
      ensures fresh(Repr)
    {
      data := new SwapAffine(empty());
      Repr := {this, this.data};
    }

    constructor(linear a:A)
      ensures Inv()
      ensures Read() == a
      ensures Has()
      ensures fresh(Repr)
    {
      data := new SwapAffine(give(a));
      Repr := {this, this.data};
    }

    method Take() returns(linear a:A)
      modifies this, Repr
      requires Inv()
      requires Has()
      ensures Inv()
      ensures !Has()
      ensures Repr == old(Repr)
      ensures a == old(Read())
    {
      linear var x := data.Swap(empty());
      a := unwrap(x);
    }

    method Give(linear a:A)
      modifies this, Repr
      requires Inv()
      requires !Has()
      ensures Inv()
      ensures Has()
      ensures a == Read()
      ensures Repr == old(Repr)
    {
      linear var x := data.Swap(give(a));
      var _ := discard(x);
    }

    function method{:caller_must_be_pure} Borrow():(shared a:A)
      reads this, Repr
      requires Inv()
      requires Has()
      ensures a == Read()
    {
      peek(data.Borrow())
    }
  }

  class BoxedLinearOption<A>
  {
    var data:SwapLinear<lOption<A>>
    ghost var Repr:set<object>
    ghost var DataInv:(lOption<A>)->bool

    predicate Inv()
      reads this, Repr
    {
      && Repr == {this, this.data}
      && DataInv == data.Inv()
    }

    function Has():bool
      requires Inv()
      reads this, Repr
    {
      data.Read().lSome?
    }

    function Read():A
      requires Inv()
      reads this, Repr
    {
      var a:A :| true;
      match data.Read() case lNone => a case lSome(a) => a
    }

    // TODO: it would be nice if this were DestructorFunction<A>, or just (linear A)->()
    constructor Empty(d:DestructorFunction<lOption<A>>)
      requires OfDestructor(d).requires(lNone)
      ensures Inv()
      ensures !Has()
      ensures fresh(Repr)
      ensures DataInv == OfDestructor(d).requires
    {
      data := new SwapLinear(lNone, d);
      Repr := {this, this.data};
      DataInv := OfDestructor(d).requires;
    }

    constructor(linear a:A, d:DestructorFunction<lOption<A>>)
      requires OfDestructor(d).requires(lSome(a))
      ensures Inv()
      ensures Read() == a
      ensures Has()
      ensures fresh(Repr)
      ensures DataInv == OfDestructor(d).requires
    {
      data := new SwapLinear(lSome(a), d);
      Repr := {this, this.data};
      DataInv := OfDestructor(d).requires;
    }

    method Take() returns(linear a:A)
      modifies this, Repr
      requires Inv()
      requires Has()
      requires DataInv(lNone)
      ensures Inv()
      ensures !Has()
      ensures Repr == old(Repr)
      ensures DataInv == old(DataInv)
      ensures a == old(Read())
      ensures DataInv(lSome(a))
    {
      linear var x := data.Swap(lNone);
      linear var lSome(y) := x;
      a := y;
    }

    method Give(linear a:A)
      modifies this, Repr
      requires Inv()
      requires !Has()
      requires DataInv(lSome(a))
      ensures Inv()
      ensures Has()
      ensures a == Read()
      ensures Repr == old(Repr)
      ensures DataInv == old(DataInv)
    {
      linear var x := data.Swap(lSome(a));
      linear match x case lNone => {}
    }

    function method{:caller_must_be_pure} Borrow():(shared a:A)
      reads this, Repr
      requires Inv()
      requires Has()
      ensures a == Read()
    {
      data.Borrow().value
    }
  }
} // module
