include "LinearBox.s.dfy"
include "LinearMaybe.s.dfy"

module LinearBox {
  import opened LinearBox_s
  import opened LinearMaybe

  class BoxedLinear<A>
  {
    var data:SwapLinear<maybe<A>>;
    ghost var Repr:set<object>;

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
      data := new SwapLinear(empty());
      Repr := {this, this.data};
    }

    constructor(linear a:A)
      ensures Inv()
      ensures Read() == a
      ensures Has()
      ensures fresh(Repr)
    {
      data := new SwapLinear(give(a));
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

} // module
