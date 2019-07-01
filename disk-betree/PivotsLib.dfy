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

  function Route(pt: PivotTable, key: Key) : int
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
  lemma GetKeyInBucket(pivotTable: PivotTable, idx: int, anyKey: Key) returns (key: Key)
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
        RouteIs(pivotTable, anyKey, 0);
        return anyKey;
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
}
