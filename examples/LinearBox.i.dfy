include "LinearBox.s.dfy"
include "LinearMaybe.s.dfy"

module LinearBox {
  import opened LinearBox_s
  import opened LinearMaybe

  class BoxedLinear<A>
  {
    var data:SwapLinear<maybe<A>>;

    function Has():bool
      reads this, data
    {
      has(data.Read())
    }

    function Read():A
      reads this, data
    {
      read(data.Read())
    }

    constructor Empty()
      ensures !Has()
      ensures fresh(this.data)
    {
      data := new SwapLinear(empty());
    }

    constructor(linear a:A)
      ensures Read() == a
      ensures Has()
      ensures fresh(this.data)
    {
      data := new SwapLinear(give(a));
    }

    method Take() returns(linear a:A)
      modifies this, data
      requires Has()
      ensures !Has()
      ensures a == old(Read())
    {
      linear var x := data.Swap(empty());
      a := unwrap(x);
    }

    method Give(linear a:A)
      modifies this, data
      requires !Has()
      ensures Has()
      ensures a == Read()
    {
      linear var x := data.Swap(give(a));
      var _ := discard(x);
    }
  }

} // module
