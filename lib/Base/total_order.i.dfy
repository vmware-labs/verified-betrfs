include "sequences.i.dfy"
include "Maps.s.dfy"
include "NativeTypes.s.dfy"
include "KeyType.s.dfy"
include "NativeArrays.s.dfy"
include "Option.s.dfy"
  
abstract module Total_Order {
  import Seq = Sequences
  import Maps
  import opened NativeTypes
  import opened Options
  import NativeArrays
  
	type Element(!new,==)

	function SomeElement() : Element

	predicate lt(a: Element, b: Element)
	{
		lte(a, b) && a != b
	}
		
	predicate lte(a: Element, b: Element)
		ensures lte(a, b) == ltedef(a, b);
		ensures ltedef(a, b) || ltedef(b, a); // Total
		ensures ltedef(a, b) && ltedef(b, a) ==> a == b; // Antisymmetric
		ensures forall a, b, c :: ltedef(a, b) && ltedef(b, c) ==> ltedef(a, c); // Transitive

	predicate ltedef(a: Element, b: Element)

  method cmp(a: Element, b: Element) returns (c: int32)
    ensures c < 0 ==> lt(a, b)
    ensures c > 0 ==> lt(b, a)
    ensures c == 0 ==> a == b

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

  lemma transitivity_le_lt(a: Element, b: Element, c: Element)
    requires lte(a,b)
    requires lt(b,c)
    ensures lt(a,c)
  {
  }

  /*method SeqMinIndex(run: seq<Element>) returns (pos: int)
    requires 0 < |run|;
    ensures 0 <= pos < |run|;
    ensures forall i {:trigger lte(run[pos], run[i]) } :: 0 <= i < |run| ==> lte(run[pos], run[i]);
  {
    pos := 0;
    var i := 1;
    while i < |run|
      invariant 0 <= i <= |run|;
      invariant pos < i;
      invariant forall j :: 0 <= j < i ==> lte(run[pos], run[j]);
    {
      if lt(run[i], run[pos]) {
        pos := i;
      }
      i := i + 1;
    }
  }

  method SeqMin(run: seq<Element>) returns (elt: Element)
    requires 0 < |run|;
    ensures elt in run;
    ensures forall elt' {:trigger lte(elt, elt') } :: elt' in run ==> lte(elt, elt');
  {
    var index := SeqMinIndex(run);
    elt := run[index];
  }
  
  method SeqMaxIndex(run: seq<Element>) returns (pos: int)
    requires 0 < |run|;
    ensures 0 <= pos < |run|;
    ensures forall i {:trigger lte(run[i], run[pos]) } :: 0 <= i < |run| ==> lte(run[i], run[pos]);
  {
    pos := 0;
    var i := 1;
    while i < |run|
      invariant 0 <= i <= |run|;
      invariant pos < i;
      invariant forall j :: 0 <= j < i ==> lte(run[j], run[pos]);
    {
      if lt(run[pos], run[i]) {
        pos := i;
      }
      i := i + 1;
    }
  }

  method SeqMax(run: seq<Element>) returns (elt: Element)
    requires 0 < |run|;
    ensures elt in run;
    ensures forall elt' {:trigger lte(elt, elt') } :: elt' in run ==> lte(elt', elt);
  {
    var index := SeqMaxIndex(run);
    elt := run[index];
  }*/
  
  predicate {:opaque} IsSorted(run: seq<Element>) {
    forall i, j :: 0 <= i <= j < |run| ==> lte(run[i], run[j])
  }

  /*method ComputeIsSorted(run: seq<Element>)
  returns (b: bool)
  ensures b == IsSorted(run)
  {
    reveal_IsSorted();
    var k := 1;
    while k < |run|
    invariant |run| > 0 ==> 0 <= k <= |run|
    invariant |run| > 0 ==> forall i, j :: 0 <= i <= j < k ==> lte(run[i], run[j])
    {
      if (!lte(run[k-1], run[k])) {
        return false;
      }
      k := k + 1;
    }
    return true;
  }*/

  predicate {:opaque} IsStrictlySorted(run: seq<Element>)
  ensures IsStrictlySorted(run) ==> IsSorted(run)
  ensures |run| == 0 ==> IsStrictlySorted(run)
  ensures |run| == 1 ==> IsStrictlySorted(run)
  {
    reveal_IsSorted();
    forall i, j :: 0 <= i < j < |run| ==> lt(run[i], run[j])
  }

  lemma IsStrictlySortedImpliesLt(run: seq<Element>, i: int, j: int)
  requires IsStrictlySorted(run)
  requires 0 <= i < j < |run|
  ensures lt(run[i], run[j])
  {
    reveal_IsStrictlySorted();
  }

  lemma IsSortedImpliesLte(run: seq<Element>, i: int, j: int)
  requires IsSorted(run)
  requires 0 <= i <= j < |run|
  ensures lte(run[i], run[j])
  {
    reveal_IsSorted();
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

  lemma strictlySortedReplace(l: seq<Element>, k: Element, pos: int)
    requires IsStrictlySorted(l)
    requires 0 <= pos < |l|
    requires 0 < pos ==> lt(l[pos-1], k)
    requires pos < |l|-1 ==> lt(k, l[pos+1])
    ensures IsStrictlySorted(l[pos := k])
  {
    var l' := l[pos := k];
    reveal_IsStrictlySorted();
    forall i, j | 0 <= i < j < |l'|
      ensures lt(l'[i], l'[j])
    {
      if i == pos {
        if pos < |l|-1 {
          assert lte(l[pos+1], l[j]);
        }
      } else if j == pos {
        if 0 < pos {
          assert lte(l[i], l[pos-1]);
        }
      }
    }
  }
  
  lemma FlattenSorted(seqs: seq<seq<Element>>)
    requires forall i :: 0 <= i < |seqs| ==> IsSorted(seqs[i])
    requires forall i, j, k1, k2 :: 0 <= i < j < |seqs| && k1 in seqs[i] && k2 in seqs[j] ==> lte(k1, k2)
    ensures IsSorted(Seq.Flatten(seqs))
  {
    var shape := Seq.FlattenShape(seqs);
    var fseqs := Seq.Flatten(seqs);
    forall i, j | 0 <= i < j < |fseqs|
      ensures lte(fseqs[i], fseqs[j])
    {
      var (il, io) := Seq.UnflattenIndex(shape, i);
      var (jl, jo) := Seq.UnflattenIndex(shape, j);
      Seq.UnflattenIndexIsCorrect(seqs, i);
      Seq.UnflattenIndexIsCorrect(seqs, j);
      Seq.UnflattenIndexOrdering(shape, i, j);
      if il < jl {
      } else {
        IsSortedImpliesLte(seqs[il], io, jo);
      }
    }
    reveal_IsSorted();
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

  lemma LargestLteIsOrderPreserving(run: seq<Element>, smaller: Element, larger: Element)
    requires IsSorted(run)
    requires lte(smaller, larger)
    ensures LargestLte(run, smaller) <= LargestLte(run, larger)
  {
  }

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

  method ArrayLargestLtePlus1Linear(run: array<Element>, start: uint64, end: uint64, needle: Element) returns (posplus1: uint64)
    requires 0 <= start as int <= end as int <= run.Length < Uint64UpperBound() / 2
    requires IsSorted(run[start..end]);
    ensures posplus1 as int == start as int + LargestLte(run[start..end], needle) + 1
  {
    var i: uint64 := start;
    var t;
    if i < end {
      t := cmp(run[i], needle);
    }
    while i < end && t <= 0
      invariant start <= i <= end
      invariant forall j :: start <= j < i ==> lte(run[j], needle)
      invariant i < end ==> (t <= 0 <==> lte(run[i], needle))
    {
      i := i + 1;
      if i < end {
        t := cmp(run[i], needle);
      }
    }
    forall j | i <= j < end
      ensures lt(needle, run[j])
    {
      reveal_IsSorted();
      assert lt(needle, run[i]);
      assert lte(run[i], run[j]);
    }
    LargestLteIsUnique(run[start..end], needle, i as int - start as int - 1);
    posplus1 := i;
  }

  method ArrayLargestLtePlus1(run: array<Element>, start: uint64, end: uint64, needle: Element) returns (posplus1: uint64)
    requires 0 <= start as int <= end as int <= run.Length < Uint64UpperBound() / 2
    requires IsSorted(run[start..end]);
    ensures posplus1 as int == start as int + LargestLte(run[start..end], needle) + 1
  {
    reveal_IsSorted();
    var lo := start;
    var hi := end;
    while 64 < hi - lo 
      invariant start <= lo <= hi <= end
      invariant forall i :: start <= i < lo ==> lte(run[i], needle)
      invariant forall i :: hi <= i < end ==> lt(needle, run[i])
      decreases hi - lo
    {
      var mid := (lo + hi) / 2;
      var t := cmp(run[mid], needle);
      if t <= 0 {
        lo := mid+1;
      } else {
        hi := mid;
      }
    }
    var i: uint64 := lo;
    var t;
    if i < hi {
      t := cmp(run[i], needle);
    }
    while i < hi && t <= 0
      invariant start <= i <= end
      invariant forall j :: start <= j < i ==> lte(run[j], needle)
      invariant i < hi ==> (t <= 0 <==> lte(run[i], needle))
    {
      i := i + 1;
      if i < hi {
        t := cmp(run[i], needle);
      }
    }
    forall j | i <= j < end
      ensures lt(needle, run[j])
    {
      reveal_IsSorted();
      assert lt(needle, run[i]);
      assert lte(run[i], run[j]);
    }
    LargestLteIsUnique(run[start..end], needle, i as int - start as int - 1);
    posplus1 := i;
  }
  
  method ArrayLargestLtPlus1(run: array<Element>, start: uint64, end: uint64, needle: Element) returns (posplus1: uint64)
    requires 0 <= start as int <= end as int <= run.Length < Uint64UpperBound() / 2
    requires IsSorted(run[start..end]);
    ensures posplus1 as int == start as int + LargestLt(run[start..end], needle) + 1
  {
    reveal_IsSorted();
    var lo := start;
    var hi := end;
    while 64 < hi - lo 
      invariant start <= lo <= hi <= end
      invariant forall i :: start <= i < lo ==> lt(run[i], needle)
      invariant forall i :: hi <= i < end ==> lte(needle, run[i])
      decreases hi - lo
    {
      var mid := (lo + hi) / 2;
      var t := cmp(run[mid], needle);
      if t < 0 {
        lo := mid;
      } else {
        hi := mid + 1;
      }
    }
    var i: uint64 := lo;
    var t;
    if i < hi {
      t := cmp(run[i], needle);
    }
    while i < hi && t < 0
      invariant start <= i <= end
      invariant forall j :: start <= j < i ==> lt(run[j], needle)
      invariant i < hi ==> (t < 0 <==> lt(run[i], needle))
    {
      i := i + 1;
      if i < hi {
        t := cmp(run[i], needle);
      }
    }
    LargestLtIsUnique(run[start..end], needle, i as int - start as int - 1);
    posplus1 := i;
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
  
  lemma StrictlySortedAugment(run: seq<Element>, key: Element)
  requires IsStrictlySorted(run)
  requires |run| > 0 ==> lt(Seq.Last(run), key)
  ensures IsStrictlySorted(run + [key])
  {
    reveal_IsStrictlySorted();
  }

  lemma StrictlySortedPop(run: seq<Element>)
  requires IsStrictlySorted(run)
  requires |run| > 0
  ensures IsStrictlySorted(Seq.DropLast(run))
  {
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
  
  lemma SetAllLtImpliesDisjoint(a: set<Element>, b: set<Element>)
    requires SetAllLt(a, b);
    ensures a !! b;
  {}

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

  method ComputeLargestLte(run: seq<Element>, needle: Element) returns (res : int64)
    requires |run| < 0x4000_0000_0000_0000
    requires IsSorted(run)
    ensures res as int == LargestLte(run, needle)
  {
    var lo: int64 := 0;
    var hi: int64 := |run| as int64;
    while lo < hi
    invariant 0 <= lo as int <= hi as int <= |run|
    invariant 1 <= lo as int ==> lte(run[lo-1], needle)
    invariant hi as int < |run| ==> lt(needle, run[hi])
    invariant lo <= hi
    decreases hi - lo
    {
      var mid := (lo + hi) / 2;
      var c := cmp(run[mid], needle);
      if (c > 0) {
        hi := mid;
      } else {
        lo := mid+1;
      }
    }

    return lo - 1;
  }

  function MapPivotedUnion<Value>(left: map<Element, Value>, pivot: Element, right: map<Element, Value>) : map<Element, Value> {
    var restricted_left := Maps.MapIRestrict(left, iset k | lt(k, pivot));
    var restricted_right := Maps.MapIRestrict(right, iset k | lte(pivot, k));
    Maps.MapDisjointUnion(restricted_left, restricted_right)
  }
    
  method ComputeLargestLt(run: seq<Element>, needle: Element) returns (res : int64)
    requires |run| < 0x4000_0000_0000_0000
    requires IsSorted(run)
    ensures res as int == LargestLt(run, needle)
  {
    var lo: int64 := 0;
    var hi: int64 := |run| as int64;
    while lo < hi
    invariant 0 <= lo as int <= hi as int <= |run|
    invariant 1 <= lo as int ==> lt(run[lo-1], needle)
    invariant hi as int < |run| ==> lte(needle, run[hi])
    decreases hi - lo
    {
      var mid := (lo + hi) / 2;
      var c := cmp(run[mid], needle);
      if (c < 0) {
        lo := mid+1;
      } else {
        hi := mid;
      }
    }

    return lo - 1;
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

  lemma StrictlySortedSeqSuccessor(s: seq<Element>, key: Element, pos: int)
    requires IsStrictlySorted(s)
    requires 0 < pos < |s|
    requires lte(s[pos-1], key)
    requires lt(key, s[pos])
    ensures SeqSuccessor(s, key) == Some(s[pos])
  {
    forall other | other in s && other != s[pos] && lt(key, other)
      ensures lt(s[pos], other)
    {
      var otherpos := Seq.IndexOf(s, other);
      IsStrictlySortedImpliesLtIndices(s, pos-1, otherpos);
      IsStrictlySortedImpliesLt(s, pos, otherpos);
    }
  }
  
  predicate {:opaque} SortedSeqForMap<V>(s: seq<(Element, V)>, m: map<Element, V>)
  {
    && IsStrictlySorted(Seq.Unzip(s).0)
    && (forall i :: 0 <= i < |s| ==> s[i].0 in m && m[s[i].0] == s[i].1)
    && (forall key :: key in m ==> (exists i :: 0 <= i < |s| && s[i].0 == key && s[i].1 == m[key]))
  }

  lemma lenSortedSeqForMap<V>(s: seq<(Element, V)>, m: map<Element, V>)
  requires SortedSeqForMap(s, m)
  ensures |s| == |m|

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

/*module Integer_Order refines Total_Order {
  type Element = int

  function SomeElement() : Element { 0 }

  predicate method lte(a: Element, b: Element) {
    reveal_ltedef();
    ltedef(a, b)
  }

  predicate method {:opaque} ltedef(a: Element, b: Element) {
    a <= b
  }

  method cmp(a: Element, b: Element) returns (c: int32)
  {
    return if a < b then -1 else if a > b then 1 else 0;
  }
}*/

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

  method cmp(a: Element, b: Element) returns (c: int32)
  {
    return if a < b then -1 else if a > b then 1 else 0;
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

  method cmp(a: Element, b: Element) returns (c: int32)
  {
    return if a < b then -1 else if a > b then 1 else 0;
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

  method cmp(a: Element, b: Element) returns (c: int32)
  {
    reveal_lte();
    reveal_ltedef();
    return if a < b then -1 else if a > b then 1 else 0;
  }
}

module Lexicographic_Byte_Order refines Total_Order {
  import KeyType
  import SeqComparison
  type Element = KeyType.Key

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

  method cmp(a: Element, b: Element) returns (c: int32)
  {
    c := NativeArrays.ByteSeqCmpByteSeq(a, b);
  }

  lemma EmptyLte(x: Element)
  ensures lte([], x)
  {
    SeqComparison.reveal_lte();
  }
}
