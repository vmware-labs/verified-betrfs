include "../Lang/NativeTypes.s.dfy"
include "../Base/sequences.i.dfy"

module Slices {
  import opened NativeTypes
  import Seq = Sequences

  datatype Slice = Slice(start: uint64, end: uint64) {
    predicate WF() {
      && start as nat <= end as nat
    }

    predicate WF'<T>(data': seq<T>) {
      && start as nat <= end as nat <= |data'|
    }

    function method I<T>(data: mseq<T>) : mseq<T>
      requires WF'(data)
    {
      data[start..end]
    }

    function method sub(a: uint64, b: uint64) : (result: Slice)
      requires WF()
      requires a <= b <= end - start
      ensures result.WF()
    {
      Slice(start + a, start + b)
    }
  }

  function method operator(| |)(slice: Slice) : (result: uint64)
    requires slice.WF()
  {
    slice.end - slice.start
  }

  function method all(data: mseq) : (result: Slice)
    ensures all(data).WF'(data)
    ensures all(data).I(data) == data
  {
    Slice(0, |data| as uint64)
  }

  predicate subSlice(smaller: Slice, superSlice: Slice)
    requires smaller.WF()
    requires superSlice.WF()
  {
    && superSlice.start <= smaller.start <= smaller.end <= superSlice.end
  }
}
