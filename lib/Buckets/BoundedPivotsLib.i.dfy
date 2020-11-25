include "../Base/total_order_impl.i.dfy"
include "../Base/KeyType.s.dfy"

//
// Provides definitions and libraries for pivot tables. A pivot
// table is a sorted list of *pivot* keys that divides the keyspace into
// contiguous ranges.
//

module BoundedPivotsLib {
  import opened Sequences
  import opened NativeTypes
  import opened KeyType
  import KeyspaceImpl = Upperbounded_Lexicographic_Byte_Order_Impl
  import Keyspace = KeyspaceImpl.Ord

  // A PivotTable of length n breaks the keyspace into n-1 "buckets"
  // For 0 <= i < n-1 then the buckets are [a_i, a_i+1) ... 
  // Each bucket must be nonempty.

  // Elements are used for providing an upperbound for the keys
  // Everything besides the last node cannot be maximum
  type Element = Keyspace.Element
  type PivotTable = seq<Element>

  predicate ElementIsKey(e: Element) 
  {
    && e.Element?
    && (|e.e| <= KeyType.MaxLen() as nat)
  }

  // all non max element must be KeyType
  predicate ElementsAreKeys(pt: PivotTable)
  {
    && (forall i | 0 <= i < |pt| && pt[i].Element? :: ElementIsKey(pt[i]))
  }

  function KeyToElement(key: Key): Element
  {
    Keyspace.Element(key)
  }

  function KeysToElements(keys: seq<Key>): (elements: seq<Element>)
  ensures |keys| == |elements|
  {
    seq (|keys|, i requires 0 <= i < |keys| => Keyspace.Element(keys[i]))
  }

  predicate WFPivots(pt: PivotTable)
  {
    && Keyspace.IsStrictlySorted(pt)
    && (forall i | 0 <= i < NumBuckets(pt) :: pt[i].Element?)
    && ElementsAreKeys(pt)
    && |pt| >= 2
  }

  predicate ContainsAllKeys(pt: PivotTable)
  {
    && WFPivots(pt)
    && pt[0] == Keyspace.Element([])
    && pt[|pt|-1] == Keyspace.Max_Element
  }

  method ComputeContainsAllKeys(pt: PivotTable) returns (b: bool)
  requires WFPivots(pt)
  requires |pt| < 0x4000_0000_0000_0000
  ensures b == ContainsAllKeys(pt)
  {
    var len := |pt| as uint64;
    var b1 := KeyspaceImpl.cmp(pt[0], Keyspace.Element([]));
    var b2 := KeyspaceImpl.cmp(pt[len - 1], Keyspace.Max_Element);
    return (b1 == 0) && (b2 == 0);
  }

  predicate BoundedKey(pt: PivotTable, key: Key)
  requires WFPivots(pt)
  {
    && Keyspace.lte(pt[0], KeyToElement(key))
    && Keyspace.lt(KeyToElement(key), pt[|pt|-1])
  }

  // allows for exclusive upperbound
  predicate ValidLeftCutOffKey(pt: PivotTable, key: Key)
  requires WFPivots(pt)
  {
    && Keyspace.lt(pt[0], KeyToElement(key))
    && Keyspace.lte(KeyToElement(key), pt[|pt|-1])
  }

  method ComputeBoundedKey(pt: PivotTable, key: Key) returns (b: bool)
  requires |pt| < 0x4000_0000_0000_0000
  requires WFPivots(pt)
  ensures b == BoundedKey(pt, key)
  {
    var pivot := Keyspace.Element(key);
    var c1 := KeyspaceImpl.cmp(pt[0], pivot);
    var c2 := KeyspaceImpl.cmp(pivot, pt[|pt| as uint64 - 1]);
    return c1 <= 0 && c2 < 0;
  }

  method ComputeValidLeftCutOffKey(pt: PivotTable, key: Key) returns (b: bool)
  requires |pt| < 0x4000_0000_0000_0000
  requires WFPivots(pt)
  ensures b == ValidLeftCutOffKey(pt, key)
  {
    var pivot := Keyspace.Element(key);
    var c1 := KeyspaceImpl.cmp(pt[0], pivot);
    var c2 := KeyspaceImpl.cmp(pivot, pt[|pt| as uint64 - 1]);
    return c1 < 0 && c2 <= 0;
  }

  predicate BoundedKeySeq(pt: PivotTable, keys: seq<Key>)
  requires WFPivots(pt)
  {
    (forall k | k in keys :: BoundedKey(pt, k))
  }

  function NumBuckets(pt: PivotTable) : int
  {
    |pt| - 1
  }

  function method PivotSize(e: Element) : (n: uint64)
  requires e.Element? ==> ElementIsKey(e)
  {
    if e.Element?
    then |e.e| as uint64
    else 0
  }
 
  function Route(pt: PivotTable, key: Key) : int
  requires WFPivots(pt)
  requires BoundedKey(pt, key)
  ensures 0 <= Route(pt, key) < NumBuckets(pt)
  {
    Keyspace.LargestLte(pt, KeyToElement(key))
  }

  method ComputeRoute(pt: PivotTable, key: Key) returns (i: uint64)
  requires |pt| < 0x4000_0000_0000_0000
  requires WFPivots(pt)
  requires BoundedKey(pt, key)
  ensures i as int == Route(pt, key)
  {
    var j := KeyspaceImpl.ComputeLargestLte(pt, Keyspace.Element(key));
    i := j as uint64;
  }

  // Quick lemma for proving that Route(pt, key) == idx
  lemma RouteIs(pt: PivotTable, key: Key, idx: int)
  requires WFPivots(pt)
  requires 0 <= idx < NumBuckets(pt)
  requires Keyspace.lte(pt[idx], KeyToElement(key));
  requires Keyspace.lt(KeyToElement(key), pt[idx+1]);
  ensures BoundedKey(pt, key)
  ensures Route(pt, key) == idx;
  {
    Keyspace.reveal_IsStrictlySorted();
  }

  // utility functions 
  function method InitPivotTable() : (pt: PivotTable)
  ensures WFPivots(pt)
  {
    var pt := [Keyspace.Element([]), Keyspace.Max_Element];
    Keyspace.reveal_IsStrictlySorted();
    pt
  }

  function GetKey(pt: PivotTable, idx: int) : (k: Key)
  requires WFPivots(pt)
  requires 0 <= idx < |pt|
  requires pt[idx].Element?
  ensures KeyToElement(k) == pt[idx]
  {
    var k := pt[idx].e;
    k
  }

  method ComputeGetKey(pt: PivotTable, idx: uint64) returns (k: Key)
  requires |pt| < 0x4000_0000_0000_0000
  requires WFPivots(pt)
  requires 0 <= idx as int < |pt|
  requires pt[idx].Element?
  ensures GetKey(pt, idx as int) == k
  ensures KeyToElement(k) == pt[idx as int]
  {
    k := pt[idx].e;
  }

  // lemma for showing every pivot except for the last one is a bounded key
  lemma PivotIsBoundedKey(pt: PivotTable, idx: int)
  requires WFPivots(pt)
  requires 0 <= idx < NumBuckets(pt)
  ensures BoundedKey(pt, pt[idx].e)
  {
    Keyspace.reveal_IsSorted();
    Keyspace.IsStrictlySortedImpliesLt(pt, idx, |pt|-1);
  }

  // Demonstrates that each bucket is non-empty
  // by returning a key in that bucket.
  lemma GetKeyInBucket(pt: PivotTable, idx: int) returns (key: Key)
  requires WFPivots(pt)
  requires 0 <= idx < NumBuckets(pt)
  ensures BoundedKey(pt, key)
  ensures Route(pt, key) == idx
  {
    PivotIsBoundedKey(pt, idx);
    Keyspace.IsStrictlySortedImpliesLt(pt, idx, idx+1);
    RouteIs(pt, pt[idx].e, idx);
    return pt[idx].e;
  }

  // removing a pivot from WFPivot is still WFPivot
  // only when there are more
  lemma WFPivotsRemoved(pt: PivotTable, idx: int)
  requires WFPivots(pt)
  requires 0 <= idx < |pt|
  requires |pt| > 2
  ensures WFPivots(remove(pt, idx))
  {
    Keyspace.reveal_IsStrictlySorted();
  }

  predicate PivotInsertable(pt: PivotTable, idx: int, key: Key)
  requires WFPivots(pt)
  {
    && 0 <= idx <= |pt|
    && (idx == 0 ==> Keyspace.lt(KeyToElement(key), pt[0]))
    && (idx == |pt| ==> Keyspace.lt(pt[|pt|-1], KeyToElement(key)))
    && (idx > 0 && idx < |pt| ==> Keyspace.lt(pt[idx-1], KeyToElement(key)) && Keyspace.lt(KeyToElement(key), pt[idx]))
    && (BoundedKey(pt, key) ==> Route(pt, key)+1 == idx)
  }

  method ComputePivotInsertable(pt: PivotTable, idx: uint64, key: Key) returns (b: bool)
  requires WFPivots(pt)
  requires |pt| < 0x4000_0000_0000_0000
  ensures b == PivotInsertable(pt, idx as int, key)
  {
    var len := |pt| as uint64;

    if idx > len {
      return false;
    }
    var pivot := Keyspace.Element(key);
    if idx == 0 {
      var c := KeyspaceImpl.cmp(pivot, pt[0]);
      if c >= 0 {
        return false;
      }
    }
    if idx == len {
      var c := KeyspaceImpl.cmp(pt[len-1], pivot);
      if c >= 0 {
        return false;
      }
    }
    if idx > 0 && idx < len {
      var c1 := KeyspaceImpl.cmp(pt[idx-1], pivot);
      var c2 := KeyspaceImpl.cmp(pivot, pt[idx]);
      if c1 >= 0 || c2 >= 0 {
        return false;
      }
    }
    var bounded := ComputeBoundedKey(pt, key);
    if bounded {
      var r := ComputeRoute(pt, key);
      if r+1 != idx {
        return false;
      }
    }
    return true;
  }

  function InsertPivot(pt: PivotTable, idx: int, key: Key) : PivotTable
  requires WFPivots(pt)
  requires PivotInsertable(pt, idx, key)
  {
    insert(pt, KeyToElement(key), idx)
  }

  lemma WFPivotsInsert(pt: PivotTable, idx: int, key: Key)
  requires WFPivots(pt)
  requires PivotInsertable(pt, idx, key);
  ensures WFPivots(InsertPivot(pt, idx, key))
  {
    assert key == KeyToElement(key).e; // observe
    Keyspace.reveal_IsStrictlySorted();
    Sequences.reveal_insert();
  }

  lemma WFSlice(pt: PivotTable, i: int, j: int)
  requires WFPivots(pt)
  requires 0 <= i <= j <= |pt|
  requires j - i > 1
  ensures WFPivots(pt[i .. j])
  {
    Keyspace.reveal_IsStrictlySorted();
  }

  lemma WFSuffix(pt: PivotTable, i: int)
  requires WFPivots(pt)
  requires 0 <= i <= |pt|
  requires |pt| - i > 1
  ensures WFPivots(pt[i .. ])
  {
    WFSlice(pt, i, |pt|);
    assert pt[i .. ] == pt[i .. |pt|];
  }

  lemma WFConcat3(left: PivotTable, key: Key, right: PivotTable)
  requires WFPivots(left)
  requires WFPivots(right)
  requires Keyspace.lt(left[|left|-1], KeyToElement(key))
  requires Keyspace.lt(KeyToElement(key), right[0])
  ensures WFPivots(concat3(left, KeyToElement(key), right))
  {
    Keyspace.reveal_IsStrictlySorted();
    reveal_concat3();
    var run := concat3(left, KeyToElement(key), right);

    forall i, j | 0 <= i < j < |run|
    ensures Keyspace.lt(run[i], run[j])
    {
      if (i < |left|) {
        if (j < |left|) {
          assert Keyspace.lt(run[i], run[j]);
        } else if (j == |left|) {
          assert Keyspace.lt(run[i], run[j]);
        } else {
          assert run[i] == left[i];
          assert run[j] == right[j - |left| - 1];
          assert Keyspace.lte(left[i], Last(left));
          assert Keyspace.lte(right[0], right[j - |left| - 1]);
          assert Keyspace.lt(run[i], run[j]);
        }
      } else if (i == |left|) {
        assert j > |left|;
        assert run[j] == right[j - |left| - 1];
        assert Keyspace.lte(right[0], right[j - |left| - 1]);
        assert Keyspace.lt(run[i], run[j]);
      } else {
        assert j > |left|;
        assert run[i] == right[i - |left| - 1];
        assert run[j] == right[j - |left| - 1];
        assert Keyspace.lt(run[i], run[j]);
      }
    }
  }

  function {:opaque} CutoffForLeft(pt: PivotTable, pivot: Key) : int
  requires WFPivots(pt)
  requires ValidLeftCutOffKey(pt, pivot)
  ensures 0 <= CutoffForLeft(pt, pivot) < NumBuckets(pt)
  ensures forall i | 0 <= i <= CutoffForLeft(pt, pivot) :: Keyspace.lt(pt[i], KeyToElement(pivot));
  ensures forall i | CutoffForLeft(pt, pivot) < i < |pt| :: Keyspace.lte(KeyToElement(pivot), pt[i]);
  {
    Keyspace.LargestLt(pt, KeyToElement(pivot))
  }

  method ComputeCutoffForLeft(pt: PivotTable, pivot: Key) returns (i: uint64)
  requires |pt| < 0x4000_0000_0000_0000
  requires WFPivots(pt)
  requires ValidLeftCutOffKey(pt, pivot)
  ensures i as int == CutoffForLeft(pt, pivot)
  {
    reveal_CutoffForLeft();
    var j := KeyspaceImpl.ComputeLargestLt(pt, Keyspace.Element(pivot)); 
    i := (j) as uint64;
  }
  
  function SplitLeft(pt: PivotTable, pivot: Key): (ret: PivotTable)
  requires WFPivots(pt)
  requires ValidLeftCutOffKey(pt, pivot)
  ensures WFPivots(ret)
  {
    var ret := pt[..CutoffForLeft(pt, pivot)+1] + [KeyToElement(pivot)];
    Keyspace.reveal_IsStrictlySorted();
    ret
  }

  method ComputeSplitLeft(pt: PivotTable, pivot: Key, cLeft: uint64) returns (ret: PivotTable)
  requires |pt| < 0x4000_0000_0000_0000
  requires WFPivots(pt)
  requires ValidLeftCutOffKey(pt, pivot)
  requires cLeft as int == CutoffForLeft(pt, pivot)
  ensures ret == SplitLeft(pt, pivot)
  {
    ret := pt[..cLeft+1] + [Keyspace.Element(pivot)];
    Keyspace.reveal_IsStrictlySorted();
  }

  function {:opaque} CutoffForRight(pt: PivotTable, pivot: Key) : int
  requires WFPivots(pt)
  requires BoundedKey(pt, pivot)
  ensures 0 <= CutoffForRight(pt, pivot) < NumBuckets(pt)
  ensures forall i | 0 <= i <= CutoffForRight(pt, pivot) :: Keyspace.lte(pt[i], KeyToElement(pivot));
  ensures forall i | CutoffForRight(pt, pivot) < i < |pt| :: Keyspace.lt(KeyToElement(pivot), pt[i]);
  {
    Route(pt, pivot)
  }

  method ComputeCutoffForRight(pt: PivotTable, pivot: Key) returns (i: uint64)
  requires |pt| < 0x4000_0000_0000_0000
  requires WFPivots(pt)
  requires BoundedKey(pt, pivot)
  ensures i as int == CutoffForRight(pt, pivot)
  {
    reveal_CutoffForRight();
    var j := ComputeRoute(pt, pivot);
    i := (j) as uint64;
  }

  function SplitRight(pt: PivotTable, pivot: Key): (ret: PivotTable)
  requires WFPivots(pt)
  requires BoundedKey(pt, pivot)
  ensures WFPivots(ret)
  {
    var ret := [KeyToElement(pivot)] + pt[CutoffForRight(pt, pivot)+1..];
    Keyspace.reveal_IsStrictlySorted();
    ret
  }

  method ComputeSplitRight(pt: PivotTable, pivot: Key, cRight: uint64) returns (ret: PivotTable)
  requires |pt| < 0x4000_0000_0000_0000
  requires WFPivots(pt)
  requires BoundedKey(pt, pivot)
  requires cRight as int == CutoffForRight(pt, pivot)
  ensures ret == SplitRight(pt, pivot)
  {
    ret := [Keyspace.Element(pivot)] + pt[cRight+1..];
    Keyspace.reveal_IsStrictlySorted();
  } 

  function PivotTableBucketKeySet(pt: PivotTable, i: int) : iset<Key>
  requires WFPivots(pt)
  requires 0 <= i < NumBuckets(pt)
  {
    iset key | BoundedKey(pt, key) && Route(pt, key) == i
  }

  // given a key that maps in the parents pivot table (by parentIdx), shows that the key maps in the child as well
  lemma GetKeyInChildBucket(parentPivots: PivotTable, childPivots: PivotTable, parentIdx: int, childIdx: int) returns (key: Key)
  requires WFPivots(parentPivots)
  requires WFPivots(childPivots)
  requires 0 <= parentIdx < NumBuckets(parentPivots)
  requires 0 <= childIdx < NumBuckets(childPivots)
  requires Keyspace.lte(parentPivots[parentIdx], childPivots[0])
  requires Keyspace.lte(Last(childPivots), parentPivots[parentIdx+1]) // only true for splitted new child
  ensures BoundedKey(parentPivots, key) && Route(parentPivots, key) == parentIdx
  ensures BoundedKey(childPivots, key) && Route(childPivots, key) == childIdx
  {
    key := GetKeyInBucket(childPivots, childIdx);
    assert Route(childPivots, key) == childIdx;
    assert Route(parentPivots, key) == parentIdx;
  }
}
