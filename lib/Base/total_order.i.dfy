include "sequences.i.dfy"
include "Maps.s.dfy"
include "../Lang/NativeTypes.s.dfy"
include "NativeArrays.s.dfy"
include "Option.s.dfy"

abstract module Total_Preorder {
  import Seq = Sequences
  
	type Element(!new,==)

	predicate lt(a: Element, b: Element)
	{
		lte(a, b) && a != b
	}
		
	predicate lte(a: Element, b: Element)
		ensures lte(a, b) == ltedef(a, b);
		ensures ltedef(a, b) || ltedef(b, a); // Total
		ensures forall a, b, c :: ltedef(a, b) && ltedef(b, c) ==> ltedef(a, c); // Transitive

	predicate ltedef(a: Element, b: Element)

  function Min(a: Element, b: Element) : Element
  {
    if lte(a, b) then a else b
  }
    
  function Max(a: Element, b: Element) : Element
  {
    if lte(a, b) then b else a
  }

  lemma transitivity_le_le(a: Element, b: Element, c: Element)
    requires lte(a,b)
    requires lte(b,c)
    ensures lte(a,c)
  {
  }

  predicate {:opaque} IsSorted(run: seq<Element>)
    ensures |run| == 0 ==> IsSorted(run)
    ensures |run| == 1 ==> IsSorted(run)
  {
    forall i, j :: 0 <= i <= j < |run| ==> lte(run[i], run[j])
  }

  predicate IsStrictlySortedInternal(run: seq<Element>)
  {
    forall i, j :: 0 <= i < j < |run| ==> lt(run[i], run[j])
  }

  lemma StrictlySortedImpliesSorted(run: seq<Element>)
    requires IsStrictlySortedInternal(run)
    ensures IsSorted(run)
  {
    forall i, j | 0 <= i <= j < |run|
      ensures lte(run[i], run[j])
    {
    }
    reveal_IsSorted();
  }
  
  predicate {:opaque} IsStrictlySorted(run: seq<Element>)
    ensures |run| == 0 ==> IsStrictlySorted(run)
    ensures |run| == 1 ==> IsStrictlySorted(run)
    ensures IsStrictlySorted(run) ==> IsSorted(run)
  {
    var b := IsStrictlySortedInternal(run);
    if b then
      StrictlySortedImpliesSorted(run);
      b
    else
      b
  }

  lemma StrictlySortedImpliesNoDupes(run: seq<Element>)
    requires IsStrictlySorted(run)
    ensures Seq.NoDupes(run)
  {
    reveal_IsStrictlySorted();
    Seq.reveal_NoDupes();
  }
  
  lemma IsSortedImpliesLte(run: seq<Element>, i: int, j: int)
  requires IsSorted(run)
  requires 0 <= i <= j < |run|
  ensures lte(run[i], run[j])
  {
    reveal_IsSorted();
  }

  lemma IsStrictlySortedImpliesLte(run: seq<Element>, i: int, j: int)
  requires IsStrictlySorted(run)
  requires 0 <= i <= j < |run|
  ensures lte(run[i], run[j])
  {
    reveal_IsStrictlySorted();
  }

  lemma IsStrictlySortedImpliesIsSorted(run: seq<Element>)
  requires IsStrictlySorted(run);
  ensures IsSorted(run);
  {
    reveal_IsSorted();
    reveal_IsStrictlySorted();
  }

  lemma SortedSubsequence(run: seq<Element>, i: int, j: int)
    requires IsSorted(run)
    requires 0 <= i <= j <= |run|
    ensures IsSorted(run[i..j])
  {
    reveal_IsSorted();
  }

  lemma StrictlySortedSubsequence(run: seq<Element>, i: int, j: int)
    requires IsStrictlySorted(run)
    requires 0 <= i <= j <= |run|
    ensures IsStrictlySorted(run[i..j])
  {
    reveal_IsStrictlySorted();
  }

//~  lemma FlattenSorted(seqs: seq<seq<Element>>)
//~    requires forall i :: 0 <= i < |seqs| ==> IsSorted(seqs[i])
//~    requires forall i, j, k1, k2 :: 0 <= i < j < |seqs| && k1 in seqs[i] && k2 in seqs[j] ==> lte(k1, k2)
//~    ensures IsSorted(Seq.Flatten(seqs))
//~  {
//~    var shape := Seq.FlattenShape(seqs);
//~    var fseqs := Seq.Flatten(seqs);
//~    forall i, j | 0 <= i < j < |fseqs|
//~      ensures lte(fseqs[i], fseqs[j])
//~    {
//~      var (il, io) := Seq.UnflattenIndex(shape, i);
//~      var (jl, jo) := Seq.UnflattenIndex(shape, j);
//~      Seq.UnflattenIndexIsCorrect(seqs, i);
//~      Seq.UnflattenIndexIsCorrect(seqs, j);
//~      Seq.UnflattenIndexOrdering(shape, i, j);
//~      if il < jl {
//~      } else {
//~        IsSortedImpliesLte(seqs[il], io, jo);
//~      }
//~    }
//~    reveal_IsSorted();
//~  }

  lemma SortedAugment(run: seq<Element>, key: Element)
  requires IsSorted(run)
  requires |run| > 0 ==> lte(Seq.Last(run), key)
  ensures IsSorted(run + [key])
  {
    reveal_IsSorted();
  }

//~  lemma SortedPrepend(key: Element, run: seq<Element>)
//~    requires IsSorted(run)
//~    requires 0 < |run| ==> lte(key, run[0])
//~    ensures IsSorted([key] + run)
//~  {
//~    reveal_IsSorted();
//~  }
  
//~  lemma StrictlySortedPop(run: seq<Element>)
//~  requires IsStrictlySorted(run)
//~  requires |run| > 0
//~  ensures IsStrictlySorted(Seq.DropLast(run))
//~  {
//~    reveal_IsStrictlySorted();
//~  }
  
}

abstract module Total_Order refines Total_Preorder {
  import Maps
  import opened NativeTypes
  import opened Options
  import NativeArrays
  
	type Element(!new,==)

	function SomeElement() : Element

	predicate lte(a: Element, b: Element)
		ensures lte(a, b) == ltedef(a, b);
		ensures ltedef(a, b) || ltedef(b, a); // Total
		ensures ltedef(a, b) && ltedef(b, a) ==> a == b; // Antisymmetric
		ensures forall a, b, c :: ltedef(a, b) && ltedef(b, c) ==> ltedef(a, c); // Transitive

	predicate ltedef(a: Element, b: Element)

  lemma transitivity_le_lt(a: Element, b: Element, c: Element)
    requires lte(a,b)
    requires lt(b,c)
    ensures lt(a,c)
  {
  }

  lemma IsStrictlySortedImpliesLt(run: seq<Element>, i: int, j: int)
  requires IsStrictlySorted(run)
  requires 0 <= i < j < |run|
  ensures lt(run[i], run[j])
  {
    reveal_IsStrictlySorted();
  }

  lemma IsStrictlySortedImpliesLtIndices(run: seq<Element>, i: int, j: int)
  requires IsStrictlySorted(run)
  requires 0 <= i < |run|
  requires 0 <= j < |run|
  requires lt(run[i], run[j])
  ensures 0 <= i < j < |run|
  {
    reveal_IsStrictlySorted();
  }

  lemma StrictlySortedEq(run1: seq<Element>, run2: seq<Element>)
    requires IsStrictlySorted(run1)
    requires IsStrictlySorted(run2)
    requires Seq.Set(run1) == Seq.Set(run2)
    ensures run1 == run2
  {
    if |run1| == 0 {
      if 0 < |run2| {
        assert run2[0] in Seq.Set(run2);
        assert false;
      }
    } else {
      assert run1[0] in Seq.Set(run2);
      var last1 := Seq.Last(run1);
      var last2 := Seq.Last(run2);
      assert last1 in Seq.Set(run1);
      assert last1 == maximum(Seq.Set(run1)) by {
        reveal_IsStrictlySorted();
      }
      assert last2 in Seq.Set(run2);
      assert last2 == maximum(Seq.Set(run2)) by {
        reveal_IsStrictlySorted();
      }
      assert last1 == last2;
      StrictlySortedSubsequence(run1, 0, |run1|-1);
      StrictlySortedSubsequence(run2, 0, |run2|-1);
      assert Seq.Set(Seq.DropLast(run1)) == Seq.Set(run1) - {last1} by {
        reveal_IsStrictlySorted();
      }
      assert Seq.Set(Seq.DropLast(run2)) == Seq.Set(run2) - {last2} by {
        reveal_IsStrictlySorted();
      }
      StrictlySortedEq(Seq.DropLast(run1), Seq.DropLast(run2));
    }
  }
  
  function LargestLte(run: seq<Element>, needle: Element) : int
    requires IsSorted(run);
    ensures -1 <= LargestLte(run, needle) < |run|;
    ensures forall i :: 0 <= i <= LargestLte(run, needle) ==> lte(run[i], needle);
    ensures forall i :: LargestLte(run, needle) < i < |run| ==> lt(needle, run[i]);
    ensures needle in run ==> 0 <= LargestLte(run, needle) && run[LargestLte(run, needle)] == needle;
  {
    reveal_IsSorted();
    if |run| == 0 || lt(needle, run[0]) then -1
    else 1 + LargestLte(run[1..], needle)
  }

//~  lemma LargestLteIsOrderPreserving(run: seq<Element>, smaller: Element, larger: Element)
//~    requires IsSorted(run)
//~    requires lte(smaller, larger)
//~    ensures LargestLte(run, smaller) <= LargestLte(run, larger)
//~  {
//~  }

  lemma LargestLteIsUnique(run: seq<Element>, needle: Element, pos: int)
    requires IsSorted(run)
    requires -1 <= pos < |run|
    requires forall i ::   0 <= i <= pos   ==> lte(run[i], needle)
    requires forall i :: pos < i < |run| ==> lt(needle, run[i])
    ensures pos == LargestLte(run, needle)
  {
    reveal_IsSorted();
    var llte := LargestLte(run, needle);
    if pos < llte {
      assert lt(run[llte], needle);
      assert lte(needle, run[llte]);
      assert false;
    } else if llte < pos {
      assert lt(run[pos], needle);
      assert lte(needle, run[pos]);
      assert false;
    }
  }

  lemma LargestLteIsUnique2(run: seq<Element>, needle: Element, pos: int)
    requires IsSorted(run)
    requires -1 <= pos < |run|
    requires 0 <= pos ==> lte(run[pos], needle)
    requires pos < |run|-1 ==> lt(needle, run[pos+1])
    ensures pos == LargestLte(run, needle)
  {
    forall i | 0 <= i <= pos
      ensures lte(run[i], needle)
    {
      IsSortedImpliesLte(run, i, pos);
    }
    forall i | pos < i < |run|
      ensures lt(needle, run[i])
    {
      IsSortedImpliesLte(run, pos+1, i);
    }
    LargestLteIsUnique(run, needle, pos);
  }
  
  lemma PosEqLargestLte(run: seq<Element>, key: Element, pos: int)
  requires IsStrictlySorted(run);
  requires 0 <= pos < |run|
  requires run[pos] == key;
  ensures pos == LargestLte(run, key);
  {
    reveal_IsStrictlySorted();
  }

  lemma PosEqLargestLteForAllElts(run: seq<Element>)
    requires IsStrictlySorted(run)
    ensures forall elt :: elt in run ==> Seq.IndexOf(run, elt) == LargestLte(run, elt)
  {
    reveal_IsStrictlySorted();
  }

  lemma LargestLteSubsequence(run: seq<Element>, needle: Element, from: int, to: int)
    requires IsSorted(run)
    requires 0 <= from <= to <= |run|
    ensures from-1 <= LargestLte(run, needle) < to ==> LargestLte(run, needle) == from + LargestLte(run[from..to], needle)
    ensures 0 <= LargestLte(run[from..to], needle) < to - from - 1 ==> LargestLte(run, needle) == from + LargestLte(run[from..to], needle)
  {
    var sub := run[from..to];
    var runllte := LargestLte(run, needle);
    var subllte := LargestLte(sub, needle);
    
    if from-1 <= runllte < to {
      if from <= runllte {
        assert lte(sub[runllte-from], needle);
      }
      if runllte < to-1 {
        assert lt(needle, sub[runllte+1-from]);
      }
      LargestLteIsUnique2(sub, needle, runllte-from);
    }

    if 0 <= subllte < |sub|-1 {
      assert lte(run[from + subllte], needle);
      assert lt(needle, sub[subllte+1]);
      assert lt(needle, run[from + subllte + 1]);
      LargestLteIsUnique2(run, needle, from + subllte);
    }
  }

  function LargestLt(run: seq<Element>, needle: Element) : int
    requires IsSorted(run);
    ensures -1 <= LargestLt(run, needle) < |run|;
    ensures forall i :: 0 <= i <= LargestLt(run, needle) ==> lt(run[i], needle);
    ensures forall i :: LargestLt(run, needle) < i < |run| ==> lte(needle, run[i]);
    ensures needle in run ==> LargestLt(run, needle) + 1 < |run| && run[LargestLt(run, needle) + 1] == needle;
  {
    reveal_IsSorted();
    if |run| == 0 || lte(needle, run[0]) then -1
    else 1 + LargestLt(run[1..], needle)
  }

  lemma LargestLtIsUnique(run: seq<Element>, needle: Element, pos: int)
    requires IsSorted(run)
    requires -1 <= pos < |run|
    requires forall i ::   0 <= i <= pos   ==> lt(run[i], needle)
    requires forall i :: pos < i < |run| ==> lte(needle, run[i])
    ensures pos == LargestLt(run, needle)
  {
    reveal_IsSorted();
    var llt := LargestLt(run, needle);
    if pos < llt {
      assert lt(run[llt], needle);
      assert lte(needle, run[llt]);
      assert false;
    } else if llt < pos {
      assert lt(run[pos], needle);
      assert lte(needle, run[pos]);
      assert false;
    }
  }
  
  function IndexOfFirstGte(run: seq<Element>, needle: Element) : (result: nat)
    requires IsSorted(run)
    ensures result <= |run|
    ensures forall i | 0 <= i < result :: lt(run[i], needle)
    ensures forall i | result <= i < |run| :: lte(needle, run[i])
  {
    reveal_IsSorted();
    if |run| == 0 then
      0
    else if lt(Seq.Last(run), needle) then
      |run|
    else
      SortedSubsequence(run, 0, |run|-1);
      IndexOfFirstGte(Seq.DropLast(run), needle)
  }

  lemma IndexOfFirstGteIsUnique(run: seq<Element>, needle: Element, idx: nat)
    requires IsSorted(run)
    requires idx <= |run|
    requires forall i | 0 <= i < idx :: lt(run[i], needle)
    requires forall i | idx <= i < |run| :: lte(needle, run[i])
    ensures idx == IndexOfFirstGte(run, needle)
  {
    reveal_IsSorted();
  }

//~  lemma IndexOfFirstGteIsOrderPreserving(run: seq<Element>, needle1: Element, needle2: Element)
//~    requires IsSorted(run)
//~    requires lte(needle1, needle2)
//~    ensures IndexOfFirstGte(run, needle1) <= IndexOfFirstGte(run, needle2)
//~  {
//~  }

  function binarySearchIndexOfFirstKeyGteIter(s: seq<Element>, key: Element, lo: int, hi: int) : (i: int)
  requires 0 <= lo < hi <= |s| + 1
  requires lo > 0 ==> lt(s[lo-1], key)
  requires hi <= |s| ==> lte(key, s[hi-1])
  ensures 0 <= i <= |s|
  ensures i > 0 ==> lt(s[i-1], key)
  ensures i < |s| ==> lte(key, s[i])
  decreases hi - lo
  {
    if lo + 1 < hi then (
      var mid := (lo + hi) / 2;
      if lt(s[mid-1], key) then
        binarySearchIndexOfFirstKeyGteIter(s, key, mid, hi)
      else
        binarySearchIndexOfFirstKeyGteIter(s, key, lo, mid)
    ) else (
      lo
    )
  }

  function {:opaque} binarySearchIndexOfFirstKeyGte(s: seq<Element>, key: Element) : (i: int)
  ensures 0 <= i <= |s|
  ensures i > 0 ==> lt(s[i-1], key)
  ensures i < |s| ==> lte(key, s[i])
  {
    binarySearchIndexOfFirstKeyGteIter(s, key, 0, |s| + 1)
  }

  function IndexOfFirstGt(run: seq<Element>, needle: Element) : (result: nat)
    requires IsSorted(run)
    ensures result <= |run|
    ensures forall i | 0 <= i < result :: lte(run[i], needle)
    ensures forall i | result <= i < |run| :: lt(needle, run[i])
   {
    reveal_IsSorted();
    if |run| == 0 then
      0
    else if lte(Seq.Last(run), needle) then
      |run|
    else
      SortedSubsequence(run, 0, |run|-1);
      IndexOfFirstGt(Seq.DropLast(run), needle)
  }

  lemma IndexOfFirstGtIsUnique(run: seq<Element>, needle: Element, idx: nat)
    requires IsSorted(run)
    requires idx <= |run|
    requires forall i | 0 <= i < idx :: lte(run[i], needle)
    requires forall i | idx <= i < |run| :: lt(needle, run[i])
    ensures idx == IndexOfFirstGt(run, needle)
  {
    reveal_IsSorted();
  }

//~  lemma IndexOfFirstGtIsOrderPreserving(run: seq<Element>, needle1: Element, needle2: Element)
//~    requires IsSorted(run)
//~    requires lte(needle1, needle2)
//~    ensures IndexOfFirstGt(run, needle1) <= IndexOfFirstGt(run, needle2)
//~  {
//~  }
  
  function binarySearchIndexOfFirstKeyGtIter(s: seq<Element>, key: Element, lo: int, hi: int) : (i: int)
    requires 0 <= lo < hi <= |s| + 1
    requires lo > 0 ==> lte(s[lo-1], key)
    requires hi <= |s| ==> lt(key, s[hi-1])
    ensures 0 <= i <= |s|
    ensures i > 0 ==> lte(s[i-1], key)
    ensures i < |s| ==> lt(key, s[i])
    decreases hi - lo
  {
    if lo + 1 < hi then (
      var mid := (lo + hi) / 2;
      if lte(s[mid-1], key) then
        binarySearchIndexOfFirstKeyGtIter(s, key, mid, hi)
      else
        binarySearchIndexOfFirstKeyGtIter(s, key, lo, mid)
    ) else (
      lo
    )
  }

  function {:opaque} binarySearchIndexOfFirstKeyGt(s: seq<Element>, key: Element) : (i: int)
    ensures 0 <= i <= |s|
    ensures i > 0 ==> lte(s[i-1], key)
    ensures i < |s| ==> lt(key, s[i])
  {
    binarySearchIndexOfFirstKeyGtIter(s, key, 0, |s| + 1)
  }

  lemma strictlySortedInsert(l: seq<Element>, k: Element, pos: int)
  requires -1 <= pos < |l|;
  requires IsStrictlySorted(l);
  requires IsSorted(l);
  requires pos == LargestLte(l, k);
  requires pos < 0 || k != l[pos];
  ensures IsStrictlySorted(Seq.insert(l, k, pos+1));
  {
    Seq.reveal_insert();
    var l' := l[..pos+1] + [k] + l[pos+1..];
    reveal_IsStrictlySorted();

    forall i, j | 0 <= i < j < |l'|
    ensures lt(l'[i], l'[j])
    {
    }
  }

  lemma strictlySortedInsert2(l: seq<Element>, k: Element, pos: int)
    requires IsStrictlySorted(l);
    requires 0 <= pos <= |l|;
    requires 0 < pos ==> lt(l[pos-1], k);
    requires pos < |l| ==> lt(k, l[pos]);
    ensures IsStrictlySorted(Seq.insert(l, k, pos));
  {
    Seq.reveal_insert();
    reveal_IsStrictlySorted();
  }

//~  lemma strictlySortedReplace(l: seq<Element>, k: Element, pos: int)
//~    requires IsStrictlySorted(l)
//~    requires 0 <= pos < |l|
//~    requires 0 < pos ==> lt(l[pos-1], k)
//~    requires pos < |l|-1 ==> lt(k, l[pos+1])
//~    ensures IsStrictlySorted(l[pos := k])
//~  {
//~    var l' := l[pos := k];
//~    reveal_IsStrictlySorted();
//~    forall i, j | 0 <= i < j < |l'|
//~      ensures lt(l'[i], l'[j])
//~    {
//~      if i == pos {
//~        if pos < |l|-1 {
//~          assert lte(l[pos+1], l[j]);
//~        }
//~      } else if j == pos {
//~        if 0 < pos {
//~          assert lte(l[i], l[pos-1]);
//~        }
//~      }
//~    }
//~  }

  lemma StrictlySortedAugment(run: seq<Element>, key: Element)
    requires IsStrictlySorted(run)
    requires |run| > 0 ==> lt(Seq.Last(run), key)
    ensures IsStrictlySorted(run + [key])
  {
    reveal_IsStrictlySorted();
  }


  lemma FlattenStrictlySorted(seqs: seq<seq<Element>>)
    requires forall i :: 0 <= i < |seqs| ==> IsStrictlySorted(seqs[i])
    requires forall i, j, k1, k2 :: 0 <= i < j < |seqs| && k1 in seqs[i] && k2 in seqs[j] ==> lt(k1, k2)
    ensures IsStrictlySorted(Seq.Flatten(seqs))
  {
    var shape := Seq.FlattenShape(seqs);
    var fseqs := Seq.Flatten(seqs);
    forall i, j | 0 <= i < j < |fseqs|
      ensures lt(fseqs[i], fseqs[j])
    {
      var (il, io) := Seq.UnflattenIndex(shape, i);
      var (jl, jo) := Seq.UnflattenIndex(shape, j);
      Seq.UnflattenIndexIsCorrect(seqs, i);
      Seq.UnflattenIndexIsCorrect(seqs, j);
      Seq.UnflattenIndexOrdering(shape, i, j);
      if il < jl {
      } else {
        IsStrictlySortedImpliesLt(seqs[il], io, jo);
      }
    }
    reveal_IsStrictlySorted();
  }
  
  /*method MergeRuns(run1: seq<Element>, run2: seq<Element>) returns (result: array<Element>)
    requires 0 < |run1|;
    requires IsSorted(run1);
    requires IsSorted(run2);
    ensures multiset(result[..]) == multiset(run1) + multiset(run2);
    ensures IsSorted(result[..]);
  {
    reveal_IsSorted();
    result := new Element[|run1| + |run2|](_ => run1[0]);
    var i1 := 0;
    var i2 := 0;

    // This awkward way of writing the expression is to work around a dafny bug:
    // https://github.com/dafny-lang/dafny/issues/353
    assert (
      var a := result[0..i1+i2];
      var b := run1[0..i1];
      var c := run2[0..i2];
      multiset(a) == multiset(b) + multiset(c)
    );
    while i1 < |run1| || i2 < |run2|
      invariant 0 <= i1 <= |run1|;
      invariant 0 <= i2 <= |run2|;
      invariant forall i, j :: 0 <= i < i1 + i2 && i1 <= j < |run1| ==> lte(result[i], run1[j]);
      invariant forall i, j :: 0 <= i < i1 + i2 && i2 <= j < |run2| ==> lte(result[i], run2[j]);
      invariant IsSorted(result[0..i1 + i2]);
      invariant (
        var a := result[0..i1+i2];
        var b := run1[0..i1];
        var c := run2[0..i2];
        multiset(a) == multiset(b) + multiset(c)
      );

      decreases |run1| + |run2| - i1 - i2;
    {
      if i1 < |run1| && i2 < |run2| {
        if lte(run1[i1], run2[i2]) {
          result[i1 + i2] := run1[i1];
          i1 := i1 + 1;
          assert run1[0..i1] == run1[0..i1-1] + run1[i1-1..i1]; // OBSERVE
        } else {
          result[i1 + i2] := run2[i2];
          i2 := i2 + 1;
          assert run2[0..i2] == run2[0..i2-1] + run2[i2-1..i2]; // OBSERVE
        }
      } else if i1 < |run1| {
          result[i1 + i2] := run1[i1];
          i1 := i1 + 1;
          assert run1[0..i1] == run1[0..i1-1] + run1[i1-1..i1];
      } else {
          result[i1 + i2] := run2[i2];
          i2 := i2 + 1;
          assert run2[0..i2] == run2[0..i2-1] + run2[i2-1..i2];
      }
    }
    assert result[..] == result[0..i1+i2]; // OBSERVE
    assert run1 == run1[0..i1]; // OBSERVE
    assert run2 == run2[0..i2]; // OBSERVE
  }

  method MergeSort(run: seq<Element>) returns (result: array<Element>)
    ensures multiset(result[..]) == multiset(run);
    ensures IsSorted(result[..]);
  {
    reveal_IsSorted();
    if |run| == 0 {
      result := new Element[|run|];
    } else if |run| <= 1 {
      result := new Element[|run|](i => run[0]);
    } else {
      var i := |run| / 2;
      ghost var run_prefix := run[..i];
      assert |multiset(run_prefix)| > 0; // OBSERVE
      assert run == run[..i] + run[i..]; // OBSERVE
      var a1 := MergeSort(run[..i]);
      var a2 := MergeSort(run[i..]);
      result :=  MergeRuns(a1[..], a2[..]);
    }
  }*/

  predicate SetAllLte(a: set<Element>, b: set<Element>) {
    forall x, y :: x in a && y in b ==> lte(x, y)
  }
  
  predicate SetAllLt(a: set<Element>, b: set<Element>) {
    forall x, y :: x in a && y in b ==> lt(x, y)
  }

  lemma SetLtLteTransitivity(a: set<Element>, b: set<Element>, c: set<Element>)
    requires SetAllLt(a, b);
    requires SetAllLte(b, c);
    requires |b| > 0;
    ensures  SetAllLt(a, c);
  {
  }
  
//~  lemma SetAllLtImpliesDisjoint(a: set<Element>, b: set<Element>)
//~    requires SetAllLt(a, b);
//~    ensures a !! b;
//~  {}

  predicate {:opaque} NotMinimum(a: Element) {
    exists b :: lt(b, a)
  }

  lemma IsNotMinimum(a: Element, b: Element)
  requires lt(a, b)
  ensures NotMinimum(b)
  {
    reveal_NotMinimum();
  }

  lemma SmallerElement(a: Element) returns (b: Element)
  requires NotMinimum(a)
  ensures lt(b, a)
  {
    reveal_NotMinimum();
    b :| lt(b, a);
  }

  function MapPivotedUnion<Value>(left: map<Element, Value>, pivot: Element, right: map<Element, Value>) : map<Element, Value> {
    var restricted_left := Maps.MapIRestrict(left, iset k | lt(k, pivot));
    var restricted_right := Maps.MapIRestrict(right, iset k | lte(pivot, k));
    Maps.MapDisjointUnion(restricted_left, restricted_right)
  }

  function SetSuccessor(m: set<Element>, key: Element) : Option<Element>
  {
    if next :|
      && next in m
      && lt(key, next)
      && (forall other :: other in m && other != next && lt(key, other) ==> lt(next, other)) then
      Some(next)
    else
      None
  }
  
  function MapSuccessor<V>(m: map<Element, V>, key: Element) : Option<Element>
  {
    SetSuccessor(m.Keys, key)
  }

  function SeqSuccessor(m: seq<Element>, key: Element) : Option<Element>
  {
    SetSuccessor(set x | x in m, key)
  }

//~  lemma StrictlySortedSeqSuccessor(s: seq<Element>, key: Element, pos: int)
//~    requires IsStrictlySorted(s)
//~    requires 0 < pos < |s|
//~    requires lte(s[pos-1], key)
//~    requires lt(key, s[pos])
//~    ensures SeqSuccessor(s, key) == Some(s[pos])
//~  {
//~    forall other | other in s && other != s[pos] && lt(key, other)
//~      ensures lt(s[pos], other)
//~    {
//~      var otherpos := Seq.IndexOf(s, other);
//~      IsStrictlySortedImpliesLtIndices(s, pos-1, otherpos);
//~      IsStrictlySortedImpliesLt(s, pos, otherpos);
//~    }
//~  }
  
  predicate {:opaque} SortedSeqForMap<V>(s: seq<(Element, V)>, m: map<Element, V>)
  {
    && IsStrictlySorted(Seq.Unzip(s).0)
    && (forall i :: 0 <= i < |s| ==> s[i].0 in m && m[s[i].0] == s[i].1)
    && (forall key :: key in m ==> (exists i :: 0 <= i < |s| && s[i].0 == key && s[i].1 == m[key]))
  }

  function {:opaque} minimum(s: set<Element>) : (x : Element)
  requires |s| >= 1
  ensures x in s
  ensures forall y | y in s :: lte(x, y)
  {
    // Implementation is pretty unimportant, the ensures clauses will
    // always suffice, as they uniquely determine the minimum.
    var a :| a in s;
    var s' := s - {a};
    if s' == {} then (
      assert s == {a};
      a
    ) else (
      var m' := minimum(s');
      if lt(a, m') then (
        assert s == {a} + s';
        a
      ) else (
        m'
      )
    )
  }

  function {:opaque} minimumOpt(s: set<Element>) : (x : Option<Element>)
  ensures x.Some? ==> x.value in s
  ensures x.Some? ==> forall y | y in s :: lte(x.value, y)
  ensures x.None? ==> s == {}
  {
    if s == {} then None else Some(minimum(s))
  }

  function {:opaque} maximum(s: set<Element>) : (x : Element)
  requires |s| >= 1
  ensures x in s
  ensures forall y | y in s :: lte(y, x)
  {
    var a :| a in s;
    var s' := s - {a};
    if s' == {} then (
      assert s == {a};
      a
    ) else (
      var m' := maximum(s');
      if lt(m', a) then (
        assert s == {a} + s';
        a
      ) else (
        m'
      )
    )
  }

  function {:opaque} maximumOpt(s: set<Element>) : (x : Option<Element>)
  ensures x.Some? ==> x.value in s
  ensures x.Some? ==> forall y | y in s :: lte(y, x.value)
  ensures x.None? ==> s == {}
  {
    if s == {} then None else Some(maximum(s))
  }
}

/*abstract module Bounded_Total_Order refines Total_Order {
  import Base_Order : Total_Order
  datatype Element = Min_Element | Element(e: Base_Order.Element) | Max_Element

  function SomeElement() : Element { Min_Element }

  predicate method lte(a: Element, b: Element) {
      || a.Min_Element?
      || b.Max_Element?
      || (a.Element? && b.Element? && Base_Order.lte(a.e, b.e))
  }

  predicate method ltedef(a: Element, b: Element) {
      || a.Min_Element?
      || b.Max_Element?
      || (a.Element? && b.Element? && Base_Order.lte(a.e, b.e))
  }
}*/


module Integer_Order refines Total_Order {
  type Element = int

  function SomeElement() : Element { 0 }

  predicate lte(a: Element, b: Element) {
    reveal_ltedef();
    ltedef(a, b)
  }

  predicate {:opaque} ltedef(a: Element, b: Element) {
    a <= b
  }
}

module Uint32_Order refines Total_Order {
  type Element = uint32

  function SomeElement() : Element { 0 }

  predicate method lte(a: Element, b: Element) {
    reveal_ltedef();
    ltedef(a, b)
  }

  predicate method {:opaque} ltedef(a: Element, b: Element) {
    a <= b
  }
}

module Uint64_Order refines Total_Order {
  type Element = uint64

  function SomeElement() : Element { 0 }

  predicate method lte(a: Element, b: Element) {
    reveal_ltedef();
    ltedef(a, b)
  }

  predicate method {:opaque} ltedef(a: Element, b: Element) {
    a <= b
  }
}


module Char_Order refines Total_Order {
  type Element = char

  function SomeElement() : Element { '\0' }

  predicate method lte(a: Element, b: Element) {
    a <= b
  }

  predicate method ltedef(a: Element, b: Element) {
    a <= b
  }
}

//module Bounded_Integer_Order refines Bounded_Total_Order {
//  import Base_Order = Integer_Order
//}

// method Main() {
//   print Integer_Order.lt(10, 11);
//   print "\n";
//   print Integer_Order.lt(11, 10);
//   print "\n";
//   print Integer_Order.lt(11, 11);
//   print "\n";
//   print Integer_Order.lte(11, 11);
//   print "\n";
// }

module Byte_Order refines Total_Order {
  type Element = byte

  function SomeElement() : Element { 0 }

  predicate method {:opaque} lte(a: Element, b: Element) {
    reveal_ltedef();
    a <= b
  }

  predicate method {:opaque} ltedef(a: Element, b: Element) {
    a <= b
  }
}

module Lexicographic_Byte_Order refines Total_Order {
  import SeqComparison
  type Element = seq<NativeTypes.byte>

  import Base_Order = Byte_Order

  function SomeElement() : Element { [] }

  predicate lte(a: Element, b: Element)
  {
    totality(a, b);
    antisymm(a, b);
    transitivity_forall();

    SeqComparison.lte(a, b)
  }

  predicate ltedef(a: Element, b: Element)
  {
    SeqComparison.lte(a, b)
  }
    
  lemma totality(a: Element, b: Element)
  ensures SeqComparison.lte(a, b) || SeqComparison.lte(b, a);
  {
    SeqComparison.reveal_lte();
  }

  lemma antisymm(a: Element, b: Element)
  ensures SeqComparison.lte(a, b) && SeqComparison.lte(b, a) ==> a == b;
  {
    SeqComparison.reveal_lte();
    if |a| > 0 && |b| > 0 {
      antisymm(a[1..], b[1..]);
    }
  }

  lemma transitivity_forall()
  ensures forall a, b, c | (SeqComparison.lte(a, b) && SeqComparison.lte(b, c)) :: SeqComparison.lte(a, c);
  {
    // We need this due to dafny bug
    // https://github.com/dafny-lang/dafny/issues/287
    SeqComparison.reveal_lte();

    forall a: Element, b: Element, c: Element | SeqComparison.lte(a, b) && SeqComparison.lte(b, c)
    ensures SeqComparison.lte(a, c)
    {
      transitivity(a, b, c);
    }
  }

  lemma transitivity(a: Element, b: Element, c: Element)
  ensures SeqComparison.lte(a, b) && SeqComparison.lte(b, c) ==> SeqComparison.lte(a, c);
  {
    SeqComparison.reveal_lte();
    if (|a| > 0 && |b| > 0 && |c| > 0) {
      transitivity(a[1..], b[1..], c[1..]);
    }
  }

  lemma EmptyLte(x: Element)
  ensures lte([], x)
  {
    SeqComparison.reveal_lte();
  }

  // TODO(robj): Ideally we'd just overload SmallerElement to return
  // [], but dafny won't let us.  :\
  lemma SmallestElement() returns (b: Element)
    ensures |b| == 0
    ensures forall a | NotMinimum(a) :: lt(b, a)
  {
    SeqComparison.reveal_lte();
    b := [];
    forall a | NotMinimum(a)
      ensures lt(b, a)
    {
      var wit := SmallerElement(a);
      if a == [] {
        assert lte(a, wit);
        assert false;
      }
    }
  }


}
