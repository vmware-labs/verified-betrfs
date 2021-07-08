include "../../../lib/Lang/NativeTypes.s.dfy"
include "../common/Limits.i.dfy"

module CircularRange {
  import opened NativeTypes
  import opened Limits

  type Index = i: int | 0 <= i < FixedSize()

  function NextIndex(i: Index): Index
  {
    if i == FixedSize() - 1 then 0 else i + 1
  }

  function PrevIndex(i: Index): Index
  {
    if i == 0 then FixedSize() - 1 else i - 1
  }

  datatype Range = 
    | Everything
    | Partial(start: Index, end: Index)
  {
    predicate HasNone()
    {
      Partial? && start == end
    }

    predicate HasSome()
    {
      !HasNone()
    }

    predicate Contains(i: Index)
    {
      match this {
        case Everything => true
        case Partial(start, end) =>
          if start <= end then
            (start <= i < end)
          else
            (start <= i || i < end)
      }
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

    function GetComplement(): Range
    {
      match this {
        case Everything => Partial(0, 0)
        case Partial(start, end) =>
          if start == end then 
            Everything
          else
            Partial(end, start)
      }
    }

    lemma ComplementCorrect(range: Range)
      ensures
        var range' := range.GetComplement();
        && range.DisjointsWith(range')
        && forall i : Index ::
          (range.Contains(i) || range'.Contains(i))
    {
    }

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

    // lemma RangeInclusion(a: Index, b: Index, c: Index)
    //   requires a != b && a != c
    //   requires Contains(Partial(a, b), c)
    //   ensures Contains(Partial(c, a), b);
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
}