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

  function method MakeDestructor<A>(linear opt:lOption<A>, d:DestructorFunction<A>):()
    requires match opt case lNone => true case lSome(a) => OfDestructor(d).requires(a)
  {
    linear match opt
      case lNone => ()
      case lSome(a) => CallDestructor(d, a)
  }

  class BoxedLinearOption<A(!new)>
  {
    var data:SwapLinear<lOption<A>>
    ghost var Repr:set<object>
    ghost var DataInv:(A)->bool

    predicate Inv()
      reads this, Repr
    {
      && Repr == {this, this.data}
      && data.Inv()(lNone)
      && (forall a:A :: DataInv(a) == data.Inv()(lSome(a)))
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

    constructor Empty(f:DestructorFunction<A>)
      ensures Inv()
      ensures !Has()
      ensures fresh(Repr)
      ensures DataInv == OfDestructor(f).requires
    {
      var d := ToDestructorEnv(MakeDestructor, f);
      data := new SwapLinear(lNone, d);
      Repr := {this, this.data};
      DataInv := OfDestructor(f).requires;
    }

    constructor(linear a:A, f:DestructorFunction<A>)
      requires OfDestructor(f).requires(a)
      ensures Inv()
      ensures Read() == a
      ensures Has()
      ensures fresh(Repr)
      ensures DataInv == OfDestructor(f).requires
    {
      var d := ToDestructorEnv(MakeDestructor, f);
      data := new SwapLinear(lSome(a), d);
      Repr := {this, this.data};
      DataInv := OfDestructor(f).requires;
    }

    method Take() returns(linear a:A)
      modifies this, Repr
      requires Inv()
      requires Has()
      ensures Inv()
      ensures !Has()
      ensures Repr == old(Repr)
      ensures DataInv == old(DataInv)
      ensures a == old(Read())
      ensures DataInv(a)
    {
      linear var x := data.Swap(lNone);
      linear var lSome(y) := x;
      a := y;
    }

    method Give(linear a:A)
      modifies this, Repr
      requires Inv()
      requires !Has()
      requires DataInv(a)
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
