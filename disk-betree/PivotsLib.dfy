include "MapSpec.dfy"
include "../lib/sequences.dfy"

module PivotsLib {
  import opened Sequences

  import MS = MapSpec
  import Keyspace = MS.Keyspace
  type Key = Keyspace.Element

  // A PivotTable of length n breaks the keyspace into n "buckets"
  // If the pivots are (a_1,...,a_n) then the buckets are
  // (-infinity, a_1)
  // [a_1, a_2)
  // ...
  // [a_(n-1), a_n)
  // [a_n, infinity)
  // Each bucket must be nonempty.
  type PivotTable = seq<Key>

  predicate WFPivots(pt: PivotTable)
  {
    && Keyspace.IsStrictlySorted(pt)
    && (|pt| > 0 ==> Keyspace.NotMinimum(pt[0]))
  }

  function NumBuckets(pt: PivotTable) : int
  {
    |pt| + 1
  }

  function method Route(pt: PivotTable, key: Key) : int
  requires WFPivots(pt)
  ensures 0 <= Route(pt, key) < NumBuckets(pt)
  {
    Keyspace.LargestLte(pt, key) + 1
  }

  // Quick lemma for proving that Route(pt, key) == idx
  lemma RouteIs(pt: PivotTable, key: Key, idx: int)
  requires WFPivots(pt)
  requires 0 <= idx <= |pt|
  requires idx > 0 ==> Keyspace.lte(pt[idx-1], key);
  requires idx < |pt| ==> Keyspace.lt(key, pt[idx]);
  ensures Route(pt, key) == idx;
  {
  }

  // Demonstrates that each bucket is non-empty
  // by returning a key in that bucket.
  // note: In the edge-case that the pivotTable is empty (so there's 1 bucket)
  // we need to pass in some key as an argument.
  // Might make sense to more generally require in Keyspace that
  // it be inhabited.
  lemma GetKeyInBucket(pivotTable: PivotTable, idx: int) returns (key: Key)
  requires WFPivots(pivotTable)
  requires 0 <= idx < NumBuckets(pivotTable)
  ensures Route(pivotTable, key) == idx
  {
    if (idx == 0) {
      if (|pivotTable| > 0) {
        var key := Keyspace.SmallerElement(pivotTable[0]);
        RouteIs(pivotTable, key, 0);
        return key;
      } else {
        var key := Keyspace.SomeElement();
        RouteIs(pivotTable, key, 0);
        return key;
      }
    } else {
      if (idx < |pivotTable|) {
        Keyspace.IsStrictlySortedImpliesLt(pivotTable, idx-1, idx);
      }
      RouteIs(pivotTable, pivotTable[idx-1], idx);
      return pivotTable[idx-1];
    }
  }

  lemma WFPivotsRemoved(pt: PivotTable, idx: int)
  requires WFPivots(pt)
  requires 0 <= idx < |pt|
  ensures WFPivots(remove(pt, idx))
  {
    Keyspace.reveal_IsStrictlySorted();
    var pt' := remove(pt, idx);
    if (|pt'| > 0) {
      if (idx == 0) {
        assert Keyspace.lt(pt[0], pt[1]);
        assert pt[1] == pt'[0];
        Keyspace.IsNotMinimum(pt[0], pt'[0]);
        assert Keyspace.NotMinimum(pt'[0]);
      } else {
        assert Keyspace.NotMinimum(pt'[0]);
      }
    }
  }

  lemma WFPivotsInsert(pt: PivotTable, idx: int, key: Key)
  requires WFPivots(pt)
  requires 0 <= idx <= |pt|
  requires Route(pt, key) == idx
  requires idx > 0 ==> key != pt[idx - 1]
  requires idx == 0 ==> Keyspace.NotMinimum(key)
  ensures WFPivots(insert(pt, key, idx))
  {
    var pt' := insert(pt, key, idx);
    Keyspace.reveal_IsStrictlySorted();
    forall i, j | 0 <= i < j < |pt'|
    ensures Keyspace.lt(pt'[i], pt'[j])
    {
      if (i == idx) {
        assert pt'[i] == key;
        assert Keyspace.lt(key, pt[idx]);
        assert Keyspace.lte(pt[idx], pt[j-1]);
        assert pt[j-1] == pt'[j];
        assert Keyspace.lt(pt'[i], pt'[j]);
      } else if (j == idx) {
        assert pt'[i] == pt[i];
        assert pt'[j] == key;
        assert Keyspace.lte(pt[i], pt[idx-1]);
        assert Keyspace.lte(pt[idx-1], key);
        assert pt[idx-1] != key;
        assert Keyspace.lt(pt[idx-1], key);
        assert Keyspace.lt(pt'[i], pt'[j]);
      } else {
        if (i < idx) { assert pt'[i] == pt[i]; }
        if (i > idx) { assert pt'[i] == pt[i-1]; }
        if (j < idx) { assert pt'[j] == pt[j]; }
        if (j > idx) { assert pt'[j] == pt[j-1]; }
        assert Keyspace.lt(pt'[i], pt'[j]);
      }
    }
  }

  lemma RouteIdenticalForInsert(pt: PivotTable, pt': PivotTable, idx: int, i: int, key: Key)
  requires WFPivots(pt)
  requires WFPivots(pt')
  requires 0 <= idx <= |pt|
  requires pt' == insert(pt, key, idx)
  requires Route(pt, key) == i
  requires i < idx
  ensures Route(pt', key) == i
  {
    RouteIs(pt', key, i);
  }

  lemma WFSlice(pt: PivotTable, i: int, j: int)
  requires WFPivots(pt)
  requires 0 <= i <= j <= |pt|
  ensures WFPivots(pt[i .. j])
  {
    Keyspace.reveal_IsStrictlySorted();

    if (i < j) {
      var e := Keyspace.SmallerElement(pt[0]);
      assert Keyspace.lte(pt[0], pt[i]);
      Keyspace.IsNotMinimum(e, pt[i]);
    }
  }

  lemma WFSuffix(pt: PivotTable, i: int)
  requires WFPivots(pt)
  requires 0 <= i <= |pt|
  ensures WFPivots(pt[i .. ])

  lemma WFConcat3(left: PivotTable, key: Key, right: PivotTable)
  requires WFPivots(left)
  requires WFPivots(right)
  requires |left| > 0 ==> Keyspace.lt(left[|left|-1], key)
  requires |right| > 0 ==> Keyspace.lt(key, right[0])
  requires Keyspace.NotMinimum(key)
  ensures WFPivots(concat3(left, key, right))

  function method {:opaque} CutoffForLeft(pivots: PivotTable, pivot: Key) : int
  requires WFPivots(pivots)
  ensures 0 <= CutoffForLeft(pivots, pivot) <= |pivots|
  ensures forall i | 0 <= i < CutoffForLeft(pivots, pivot) :: Keyspace.lt(pivots[i], pivot);
  ensures forall i | CutoffForLeft(pivots, pivot) <= i < |pivots| :: Keyspace.lte(pivot, pivots[i]);

  function method {:opaque} CutoffForRight(pivots: PivotTable, pivot: Key) : int
  requires WFPivots(pivots)
  ensures 0 <= CutoffForRight(pivots, pivot) <= |pivots|
  ensures forall i | 0 <= i < CutoffForRight(pivots, pivot) :: Keyspace.lte(pivots[i], pivot);
  ensures forall i | CutoffForRight(pivots, pivot) <= i < |pivots| :: Keyspace.lt(pivot, pivots[i]);
  {
    Route(pivots, pivot)
  }

  lemma PivotNotMinimum(pivots: PivotTable, i: int)
  requires WFPivots(pivots)
  requires 0 <= i < |pivots|
  ensures Keyspace.NotMinimum(pivots[i])
  {
    Keyspace.reveal_IsStrictlySorted();
    var e := Keyspace.SmallerElement(pivots[0]);
    assert Keyspace.lte(pivots[0], pivots[i]);
    Keyspace.IsNotMinimum(e, pivots[i]);
  }

  function PivotTableBucketKeySet(pivots: PivotTable, i: int) : iset<Key>
  requires WFPivots(pivots)
  {
    iset key | Route(pivots, key) == i
  }

  lemma GetKeyInChildBucket(parentPivots: seq<Key>, childPivots: seq<Key>, parentIdx: int, childIdx: int) returns (key: Key)
  requires WFPivots(parentPivots)
  requires WFPivots(childPivots)
  requires 0 <= parentIdx <= |parentPivots|
  requires 0 <= childIdx <= |childPivots|
  requires parentIdx > 0 && |childPivots| > 0 ==> Keyspace.lt(parentPivots[parentIdx-1], childPivots[0])
  requires parentIdx < |parentPivots| && |childPivots| > 0 ==> Keyspace.lt(Last(childPivots), parentPivots[parentIdx])
  ensures Route(parentPivots, key) == parentIdx
  ensures Route(childPivots, key) == childIdx
  {
    if (childIdx > 0) {
      key := childPivots[childIdx - 1];
      Keyspace.IsStrictlySortedImpliesLte(childPivots, childIdx - 1, |childPivots| - 1);
      Keyspace.IsStrictlySortedImpliesLte(childPivots, 0, childIdx - 1);
      RouteIs(parentPivots, key, parentIdx);
      if (childIdx < |childPivots|) {
        Keyspace.IsStrictlySortedImpliesLt(childPivots, childIdx - 1, childIdx);
      }
      RouteIs(childPivots, key, childIdx);
    } else if (parentIdx > 0) {
      key := parentPivots[parentIdx - 1];
      if (parentIdx < |parentPivots|) {
        Keyspace.IsStrictlySortedImpliesLt(parentPivots, parentIdx - 1, parentIdx);
      }
      RouteIs(parentPivots, key, parentIdx);
      RouteIs(childPivots, key, childIdx);
    } else if (|childPivots| > 0) {
      key := Keyspace.SmallerElement(childPivots[0]);
      Keyspace.IsStrictlySortedImpliesLte(childPivots, 0, |childPivots| - 1);
      RouteIs(parentPivots, key, parentIdx);
      RouteIs(childPivots, key, childIdx);
    } else if (|parentPivots| > 0) {
      key := Keyspace.SmallerElement(parentPivots[0]);
      RouteIs(parentPivots, key, parentIdx);
      RouteIs(childPivots, key, childIdx);
    } else {
      key := Keyspace.SomeElement();
      RouteIs(parentPivots, key, parentIdx);
      RouteIs(childPivots, key, childIdx);
    }
  }
}
