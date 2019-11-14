include "sequences.i.dfy"
include "NativeTypes.s.dfy"
include "KeyType.s.dfy"
  
abstract module Total_Order {
  import Seq = Sequences
  import opened NativeTypes
  import Native
    
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

  method cmp(a: Element, b: Element) returns (c: int32)
    ensures c == -1 || c == 0 || c == 1
    ensures c == -1 ==> lt(a, b)
    ensures c == 1 ==> lt(b, a)
    ensures c == 0 ==> a == b

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

  lemma PosEqLargestLte(run: seq<Element>, key: Element, pos: int)
  requires IsStrictlySorted(run);
  requires 0 <= pos < |run|
  requires run[pos] == key;
  ensures pos == LargestLte(run, key);
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
      if (c == 1) {
        hi := mid;
      } else {
        lo := mid+1;
      }
    }

    return lo - 1;
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
      if (c == -1) {
        lo := mid+1;
      } else {
        hi := mid;
      }
    }

    return lo - 1;
  }

  predicate {:opaque} SortedSeqForMap<V>(s: seq<(Element, V)>, m: map<Element, V>)
  {
    && (forall i, j | 0 <= i < j < |s| :: lt(s[i].0, s[j].0))
    && (forall i | 0 <= i < |s| :: s[i].0 in m && m[s[i].0] == s[i].1)
    && (forall key | key in m :: exists i :: 0 <= i < |s| && s[i].0 == key && s[i].1 == m[key])
  }

  function getSortedSeqForMap<V>(m : map<Element, V>) : (s: seq<(Element, V)>)
  ensures SortedSeqForMap(s, m)

  lemma lenSortedSeqForMap<V>(s: seq<(Element, V)>, m: map<Element, V>)
  requires SortedSeqForMap(s, m)
  ensures |s| == |m|
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
  type Element = KeyType.Key

  import Base_Order = Byte_Order

  function SomeElement() : Element { [] }

  predicate lte(a: Element, b: Element)
  {
    totality(a, b);
    antisymm(a, b);
    transitivity_forall();

    seq_lte(a, b)
  }

  predicate ltedef(a: Element, b: Element)
  {
    seq_lte(a, b)
  }
    
  predicate {:opaque} seq_lte(a: Element, b: Element)
  decreases |a|
  {
    if |a| == 0 then (
      true
    ) else (
      if |b| == 0 then (
        false
      ) else (
        if Base_Order.lt(a[0], b[0]) then true
        else if Base_Order.lt(b[0], a[0]) then false
        else seq_lte(a[1..], b[1..])
      )
    )
  }

  lemma totality(a: Element, b: Element)
  ensures seq_lte(a, b) || seq_lte(b, a);
  {
    reveal_seq_lte();
  }

  lemma antisymm(a: Element, b: Element)
  ensures seq_lte(a, b) && seq_lte(b, a) ==> a == b;
  {
    reveal_seq_lte();
    if |a| > 0 && |b| > 0 {
      antisymm(a[1..], b[1..]);
    }
  }

  lemma transitivity_forall()
  ensures forall a, b, c | (seq_lte(a, b) && seq_lte(b, c)) :: seq_lte(a, c);
  {
    // We need this due to dafny bug
    // https://github.com/dafny-lang/dafny/issues/287
    reveal_seq_lte();

    forall a, b, c | seq_lte(a, b) && seq_lte(b, c)
    ensures seq_lte(a, c)
    {
      transitivity(a, b, c);
    }
  }

  lemma transitivity(a: Element, b: Element, c: Element)
  ensures seq_lte(a, b) && seq_lte(b, c) ==> seq_lte(a, c);
  {
    reveal_seq_lte();
    if (|a| > 0 && |b| > 0 && |c| > 0) {
      transitivity(a[1..], b[1..], c[1..]);
    }
  }

  method cmp(a: Element, b: Element) returns (c: int32)
  {
    c := Native.Arrays.ByteSeqCmpByteSeq(a, b);
  }
}
