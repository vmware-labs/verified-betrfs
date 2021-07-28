include "../../../lib/Lang/NativeTypes.s.dfy"
include "../common/Limits.i.dfy"

module CircularRange {
  import opened NativeTypes
  import opened Limits

  type Index = i: int | 0 <= i < FixedSize()

  function method NextIndex(i: Index): Index
  {
    if i == FixedSize() - 1 then 0 else i + 1
  }

  function method PrevIndex(i: Index): Index
  {
    if i == 0 then FixedSize() - 1 else i - 1
  }

  function method WrappedDistance(s: Index, e: Index): nat
  {
    if s <= e then e - s
    else FixedSize() - s + e
  }

  function method RightShift(i: Index, n: Index) : Index
  {
    var e: int := i + n;
    if e >= FixedSize() then 
      e - FixedSize()
    else
      e
  }

  function method LeftShift(i: Index, n: Index) : Index
  {
    var e: int := i - n;
    if e < 0 then
      e + FixedSize()
    else
      e
  }

  // end is not inclusive, range will never cover the entire table

  datatype Range =
    | Complete(pivot: Index)
    | Partial(start: Index, end: Index)
  {
    predicate method HasNone()
    {
      Partial? && start == end
    }

    predicate method HasSome()
    {
      !HasNone()
    }

    predicate Contains(i: Index)
    {
      if Complete? then
        true
      else
        var Partial(start, end) := this;
        if start <= end then
          (start <= i < end)
        else
          (start <= i || i < end)
    }

    predicate OverlapsWith(other: Range)
    {
      exists i : Index ::
        (Contains(i) && other.Contains(i))
    }

    predicate DisjointsWith(other: Range)
    {
      !OverlapsWith(other)
    }

    predicate IsSuperOf(other: Range)
    {
      forall i : Index ::
        (other.Contains(i) ==> Contains(i))
    }

    predicate IsSubOf(other: Range)
    {
      forall i : Index ::
        (Contains(i) ==> other.Contains(i))
    }

    function method LeftShift1(): Range
      requires Partial?
    {
      Partial(PrevIndex(start), PrevIndex(end))
    }

    function method RightShift1(): Range
      requires Partial?
    {
      Partial(NextIndex(start), NextIndex(end))
    }

    predicate method AlmostComplete()
      requires Partial?
    {
      start == NextIndex(end)
    }

    function method RightExtend1(): Range
      requires Partial?
    {
      if start == NextIndex(end) then 
        Complete(start)
      else
        Partial(start, NextIndex(end))
    }

    function method LeftShrink1(): Range
      requires Partial?
    {
      Partial(NextIndex(start), end)
    }

    function method RightShrink1(): (r: Range)
      requires HasSome()
      ensures |r| < |this|
    {
      if Complete? then 
        Partial(pivot, PrevIndex(pivot))
      else
        Partial(start, PrevIndex(end))
    }

    // function method GetRightNext(): Index
    //   requires Partial?
    // {
    //   NextIndex(end)
    // }

    function method GetLast(): Index
      requires HasSome()
    {
      if Complete? then
        PrevIndex(pivot)
      else
        PrevIndex(end)
    }

    // function GetComplement(): Range
    // {
    //   match this {
    //     case Everything => Partial(0, 0)
    //     case Partial(start, end) =>
    //       if start == end then 
    //         Everything
    //       else
    //         Partial(end, start)
    //   }
    // }

    // lemma ComplementCorrect(range: Range)
    //   ensures
    //     var range' := range.GetComplement();
    //     && range.DisjointsWith(range')
    //     && forall i : Index ::
    //       (range.Contains(i) || range'.Contains(i))
    // {
    // }

    // lemma DisjointRangesValidBetween(a: Range, b: Range)
    //   requires !OverlapsWith(a, b)
    //   requires !a.Nothing? && !b.Nothing?
    //   ensures a.Partial? && b.Partial?
    // {
    //   if a.Everything? {
    //     if b.Partial? {
    //       assert Contains(a, b.start);
    //     } else {
    //       assert Contains(a, 0);
    //       assert Contains(b, 0);
    //     }
    //     assert false;
    //   }
      
    //   if b.Everything? {
    //     if a.Partial? {
    //       assert Contains(b, a.start);
    //     } else {
    //       assert Contains(a, 0);
    //       assert Contains(b, 0);
    //     }
    //     assert false;
    //   }

    //   assert a.Partial? && b.Partial?;
    // }

    // function GetBetween(a: Range, b: Range): Range
    //   requires !OverlapsWith(a, b)
    // {
    //   if a.Nothing? || b.Nothing? then
    //     Nothing
    //   else (
    //     DisjointRangesValidBetween(a, b);
    //     if a.end == b.start then Nothing
    //     else Partial(a.end, b.start)
    //   )
    // }

    // // if i is not in range, then i is in the copmlement (vice versa)
    // lemma RangeComplement(i: Index, range: Range)
    //   ensures !Contains(range, i) == Contains(GetComplement(range), i);
    // { 
    // }

    // lemma RangeNext(start: Index, end: Index, i: Index)
    //   requires start != end
    //   requires start != NextIndex(end)
    //   requires Contains(Partial(start, NextIndex(end)), i);
    // {
    //   assert Contains(Partial(start, end), i) || end == i;
    // }
  }

  function operator(| |)(r: Range): nat
  {
    if r.Complete? then
      FixedSize()
    else 
      WrappedDistance(r.start, r.end)
  }

  lemma RangeInclusion(a: Index, b: Index, c: Index)
    requires a != c
    requires Partial(a, b).Contains(c)
    ensures Partial(c, a).Contains(b);
  {
  }

  // lemma RangeSize(r: Range)
  //   ensures |r| == |(set i | r.Contains(i) :: i)|
  // {
  //   var indices := (set i | r.Contains(i) :: i);
  //   var Partial(start, end) := r;

  //   if start == end {
  //     assert |indices| == |r|;
  //   } else if start < end {
      
  //   } else {

  //   }
  // }

}