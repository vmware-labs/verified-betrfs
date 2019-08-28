include "Message.i.dfy"
include "../lib/sequences.s.dfy"
include "../lib/Maps.s.dfy"
include "BucketsLib.i.dfy"
include "BucketWeights.i.dfy"
include "../lib/Marshalling/Seqs.i.dfy"

module KMTable {
  import opened ValueMessage`Internal
  import opened Lexicographic_Byte_Order
  import opened Sequences
  import opened Options
  import opened Maps
  import opened BucketsLib
  import opened BucketWeights
  import opened NativeTypes
  import Native
  import P = PivotsLib

  type Key = Element

  datatype KMTable = KMTable(keys: seq<Key>, values: seq<Message>)

  predicate WF(kmt: KMTable) {
    && |kmt.keys| == |kmt.values|
    && IsStrictlySorted(kmt.keys)
    && (forall i | 0 <= i < |kmt.values| :: kmt.values[i] != IdentityMessage())
  }

  function {:opaque} I(kmt: KMTable) : Bucket
  requires |kmt.keys| == |kmt.values|
  decreases |kmt.keys|
  {
    if |kmt.keys| == 0 then map[] else (
      I(KMTable(DropLast(kmt.keys), DropLast(kmt.values)))[Last(kmt.keys) := Last(kmt.values)]
    )
  }

  function {:opaque} ISeq(kmts: seq<KMTable>) : (s : seq<Bucket>)
  requires forall i | 0 <= i < |kmts| :: |kmts[i].keys| == |kmts[i].values|
  ensures |s| == |kmts|
  ensures forall i | 0 <= i < |kmts| :: s[i] == I(kmts[i])
  {
    if |kmts| == 0 then [] else ISeq(DropLast(kmts)) + [I(Last(kmts))]
  }

  function prefix(kmt: KMTable, i: int) : KMTable
  requires 0 <= i <= |kmt.keys|
  requires 0 <= i <= |kmt.values|
  {
    KMTable(kmt.keys[..i], kmt.values[..i]) 
  }

  lemma WFPrefix(kmt: KMTable, i: int)
  requires WF(kmt)
  requires 0 <= i <= |kmt.keys|
  ensures WF(prefix(kmt, i))
  {
    reveal_IsStrictlySorted();
  }

  lemma IndexOfKey(kmt: KMTable, key: Key) returns (i : int)
  requires |kmt.keys| == |kmt.values|
  requires key in I(kmt)
  ensures 0 <= i < |kmt.keys|
  ensures kmt.keys[i] == key
  decreases |kmt.keys|
  {
    reveal_I();
    if key == Last(kmt.keys) {
      i := |kmt.keys| - 1;
    } else {
      i := IndexOfKey(KMTable(DropLast(kmt.keys), DropLast(kmt.values)), key);
    }
  }

  lemma Imaps(kmt: KMTable, i: int)
  requires WF(kmt)
  requires 0 <= i < |kmt.keys|
  ensures MapsTo(I(kmt), kmt.keys[i], kmt.values[i])
  decreases |kmt.keys|
  {
    reveal_I();
    if (i == |kmt.keys| - 1) {
    } else {
      reveal_IsStrictlySorted();
      Imaps(KMTable(DropLast(kmt.keys), DropLast(kmt.values)), i);
      assert kmt.keys[|kmt.keys| - 1] != kmt.keys[i];
    }
  }

  lemma WFImpliesWFBucket(kmt: KMTable)
  requires WF(kmt)
  ensures WFBucket(I(kmt))
  decreases |kmt.keys|
  {
    reveal_I();
    reveal_WFBucket();
    if |kmt.keys| == 0 {
    } else {
      ghost var km' := KMTable(DropLast(kmt.keys), DropLast(kmt.values));
      WFPrefix(kmt, |kmt.keys| - 1);
      assert WF(km');
      WFImpliesWFBucket(km');
    }
  }

  /////////////////////////
  //// Flush
  /////////////////////////

  function append(kmt: KMTable, key: Key, value: Message) : KMTable
  {
    KMTable(kmt.keys + [key], kmt.values + [value])
  }

  lemma Iappend(kmt: KMTable, key: Key, value: Message)
  requires |kmt.keys| == |kmt.values|
  ensures I(append(kmt, key, value)) == I(kmt)[key := value]
  {
    reveal_I();
  }

  lemma Iprefix_append(kmt: KMTable, i: int)
  requires |kmt.keys| == |kmt.values|
  requires 0 <= i < |kmt.keys|
  ensures I(prefix(kmt, i + 1)) == I(prefix(kmt, i))[kmt.keys[i] := kmt.values[i]]
  {
    assert prefix(kmt, i + 1) == append(prefix(kmt, i), kmt.keys[i], kmt.values[i]);
    Iappend(prefix(kmt, i), kmt.keys[i], kmt.values[i]);
  }

  function flushIterate(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<KMTable>, cur: KMTable) : seq<KMTable>
  requires WF(parent)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires |pivots| + 1 == |children|
  requires 0 <= parentIdx <= |parent.keys|
  requires 0 <= childrenIdx <= |children|
  requires childrenIdx < |children| ==> 0 <= childIdx <= |children[childrenIdx].keys|
  decreases |children| - childrenIdx
  decreases |parent.keys| - parentIdx +
      (if childrenIdx < |children| then |children[childrenIdx].keys| - childIdx else 0)
  {
    if childrenIdx == |children| then (
      acc
    ) else (
      var child := children[childrenIdx];

      if parentIdx == |parent.keys| then (
        if childIdx == |child.keys| then (
          flushIterate(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], KMTable([], []))
        //) else if |cur.keys| == 0 then (
        //  flushIterate(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [child], KMTable([], []))
        ) else (
          flushIterate(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], child.values[childIdx]))
        )
      ) else (
        if childIdx == |child.keys| then (
          if childrenIdx == |children| - 1 then (
            flushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.values[parentIdx]))
          ) else (
            if lt(parent.keys[parentIdx], pivots[childrenIdx]) then (
              flushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.values[parentIdx]))
            ) else (
              flushIterate(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], KMTable([], []))
            )
          )
        ) else (
          if child.keys[childIdx] == parent.keys[parentIdx] then (
            var m := Merge(parent.values[parentIdx], child.values[childIdx]);
            if m == IdentityMessage() then (
              flushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, cur)
            ) else (
              flushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], m))
            )
          ) else if lt(child.keys[childIdx], parent.keys[parentIdx]) then (
            flushIterate(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], child.values[childIdx]))
          ) else (
            flushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.values[parentIdx]))
          )
        )
      )
    )
  }

  function flush(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>) : seq<KMTable>
  requires WF(parent)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires |pivots| + 1 == |children|
  {
    flushIterate(parent, children, pivots, 0, 0, 0, [], KMTable([], []))
  }

  predicate flushIterateInv(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<KMTable>, cur: KMTable)
  {
    && WF(parent)
    && (forall i | 0 <= i < |children| :: WF(children[i]))
    && WFBucketList(ISeq(children), pivots)
    && |pivots| + 1 == |children|
    && 0 <= parentIdx <= |parent.keys|
    && 0 <= childrenIdx <= |children|
    && (childrenIdx < |children| ==> 0 <= childIdx <= |children[childrenIdx].keys|)
    && |acc| == childrenIdx
    && (forall i | 0 <= i < childrenIdx :: WF(acc[i]))
    && ISeq(acc) == BucketListFlush'(I(parent), ISeq(children), pivots, childrenIdx)
    && WF(cur)
    && (childrenIdx < |children| ==> I(cur) == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx))
    && (childrenIdx < |children| && childIdx > 0 && parentIdx < |parent.keys| ==> lt(children[childrenIdx].keys[childIdx - 1], parent.keys[parentIdx]))
    && (childrenIdx > 0 && childrenIdx - 1 < |pivots| && parentIdx < |parent.keys| ==> lte(pivots[childrenIdx - 1], parent.keys[parentIdx]))
    && (parentIdx > 0 && childrenIdx < |children| && childIdx < |children[childrenIdx].keys| ==> lt(parent.keys[parentIdx - 1], children[childrenIdx].keys[childIdx]))
    && (parentIdx > 0 && childrenIdx < |pivots| ==> lt(parent.keys[parentIdx - 1], pivots[childrenIdx]))
  }

  lemma flushIterateCurLastLt(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<KMTable>, cur: KMTable)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  requires childrenIdx < |children|
  ensures |cur.keys| > 0 && parentIdx < |parent.keys| ==> lt(cur.keys[|cur.keys| - 1], parent.keys[parentIdx])
  ensures |cur.keys| > 0 && childIdx < |children[childrenIdx].keys| ==> lt(cur.keys[|cur.keys| - 1], children[childrenIdx].keys[childIdx])
  {
    reveal_I();
    if (|cur.keys| > 0) {
      var lastCurKey := cur.keys[|cur.keys| - 1];
      assert lastCurKey in I(cur);
      assert lastCurKey in (I(prefix(parent, parentIdx)).Keys + I(prefix(children[childrenIdx], childIdx)).Keys);
      if lastCurKey in I(prefix(parent, parentIdx)).Keys {
        var i := IndexOfKey(prefix(parent, parentIdx), lastCurKey);
        assert parent.keys[i] == lastCurKey;
        if parentIdx < |parent.keys| {
          IsStrictlySortedImpliesLt(parent.keys, i, parentIdx);
        }
        if childIdx < |children[childrenIdx].keys| {
          IsStrictlySortedImpliesLte(parent.keys, i, parentIdx - 1);
        }
      } else {
        var i := IndexOfKey(prefix(children[childrenIdx], childIdx), lastCurKey);
        assert children[childrenIdx].keys[i] == lastCurKey;
        if parentIdx < |parent.keys| {
          IsStrictlySortedImpliesLte(children[childrenIdx].keys, i, childIdx - 1);
        }
        if childIdx < |children[childrenIdx].keys| {
          IsStrictlySortedImpliesLt(children[childrenIdx].keys, i, childIdx);
        }
      }
    }
  }

  lemma flushIterateNextsNotInPrefixes(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<KMTable>, cur: KMTable)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  requires childrenIdx < |children|
  ensures parentIdx < |parent.keys| ==> parent.keys[parentIdx] !in I(prefix(parent, parentIdx))
  ensures parentIdx < |parent.keys| ==> parent.keys[parentIdx] !in I(prefix(children[childrenIdx], childIdx))
  ensures childIdx < |children[childrenIdx].keys| ==> children[childrenIdx].keys[childIdx] !in I(prefix(parent, parentIdx))
  ensures childIdx < |children[childrenIdx].keys| ==> children[childrenIdx].keys[childIdx] !in I(prefix(children[childrenIdx], childIdx))
  {
    if parentIdx < |parent.keys| && parent.keys[parentIdx] in I(prefix(parent, parentIdx)) {
      var i := IndexOfKey(prefix(parent, parentIdx), parent.keys[parentIdx]);
      IsStrictlySortedImpliesLt(parent.keys, i, parentIdx);
    }
    if parentIdx < |parent.keys| && parent.keys[parentIdx] in I(prefix(children[childrenIdx], childIdx)) {
      var i := IndexOfKey(prefix(children[childrenIdx], childIdx), parent.keys[parentIdx]);
      IsStrictlySortedImpliesLte(children[childrenIdx].keys, i, childIdx - 1);
    }
    if childIdx < |children[childrenIdx].keys| && children[childrenIdx].keys[childIdx] in I(prefix(parent, parentIdx)) {
      var i := IndexOfKey(prefix(parent, parentIdx), children[childrenIdx].keys[childIdx]);
      IsStrictlySortedImpliesLte(parent.keys, i, parentIdx - 1);
    }
    if childIdx < |children[childrenIdx].keys| && children[childrenIdx].keys[childIdx] in I(prefix(children[childrenIdx], childIdx)) {
      var i := IndexOfKey(prefix(children[childrenIdx], childIdx), children[childrenIdx].keys[childIdx]);
      IsStrictlySortedImpliesLt(children[childrenIdx].keys, i, childIdx);
    }
  }

  lemma flushIterateAppendParent(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<KMTable>, cur: KMTable)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  requires 0 <= childrenIdx < |children|
  requires 0 <= parentIdx < |parent.keys|
  requires childrenIdx < |pivots| ==> lt(parent.keys[parentIdx], pivots[childrenIdx])
  ensures WF(append(cur, parent.keys[parentIdx], parent.values[parentIdx]))
  ensures I(append(cur, parent.keys[parentIdx], parent.values[parentIdx]))
      == BucketListItemFlush(I(prefix(parent, parentIdx + 1)), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx)
  {
    flushIterateCurLastLt(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
    flushIterateNextsNotInPrefixes(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
    StrictlySortedAugment(cur.keys, parent.keys[parentIdx]);
    BucketListItemFlushAddParentKey(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, parent.keys[parentIdx], parent.values[parentIdx]);

    P.RouteIs(pivots, parent.keys[parentIdx], childrenIdx);

    Iappend(cur, parent.keys[parentIdx], parent.values[parentIdx]);
    Iprefix_append(parent, parentIdx);

    /*assert I(append(cur, parent.keys[parentIdx], parent.values[parentIdx]))
        == I(cur)[parent.keys[parentIdx] := parent.values[parentIdx]]
        == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx)[parent.keys[parentIdx] := parent.values[parentIdx]]
        == BucketListItemFlush(I(prefix(parent, parentIdx))[parent.keys[parentIdx] := parent.values[parentIdx]], I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx)
        == BucketListItemFlush(I(prefix(parent, parentIdx + 1)), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx);*/
  }

  lemma flushIterateAppendChild(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<KMTable>, cur: KMTable)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  requires 0 <= childrenIdx < |children|
  requires 0 <= childIdx < |children[childrenIdx].keys|
  ensures WF(append(cur, children[childrenIdx].keys[childIdx], children[childrenIdx].values[childIdx]))
  ensures I(append(cur, children[childrenIdx].keys[childIdx], children[childrenIdx].values[childIdx]))
      == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx + 1)), pivots, childrenIdx)
  {
    var child := children[childrenIdx];
    flushIterateCurLastLt(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
    flushIterateNextsNotInPrefixes(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
    StrictlySortedAugment(cur.keys, child.keys[childIdx]);
    BucketListItemFlushAddChildKey(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, child.keys[childIdx], child.values[childIdx]);

    assert WFBucketAt(I(children[childrenIdx]), pivots, childrenIdx);
    Imaps(child, childIdx);
    assert child.keys[childIdx] in I(children[childrenIdx]);
    assert P.Route(pivots, child.keys[childIdx]) == childrenIdx;

    Iappend(cur, child.keys[childIdx], child.values[childIdx]);
    Iprefix_append(child, childIdx);

    /*assert I(append(cur, child.keys[childIdx], child.values[childIdx]))
        == I(cur)[child.keys[childIdx] := child.values[childIdx]]
        == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx)[child.keys[childIdx] := child.values[childIdx]]
        == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx))[child.keys[childIdx] := child.values[childIdx]], pivots, childrenIdx)
        == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx + 1)), pivots, childrenIdx);*/
  }

  lemma {:fuel BucketListItemFlush,0} {:fuel P.Route,0}
  flushIterateAppendParentAndChild(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<KMTable>, cur: KMTable)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  requires 0 <= childrenIdx < |children|
  requires 0 <= parentIdx < |parent.keys|
  requires 0 <= childIdx < |children[childrenIdx].keys|
  requires children[childrenIdx].keys[childIdx] == parent.keys[parentIdx]
  requires Merge(parent.values[parentIdx], children[childrenIdx].values[childIdx]) != IdentityMessage()

  ensures WF(append(cur, parent.keys[parentIdx], Merge(parent.values[parentIdx], children[childrenIdx].values[childIdx])))
  ensures I(append(cur, parent.keys[parentIdx], Merge(parent.values[parentIdx], children[childrenIdx].values[childIdx])))
      == BucketListItemFlush(I(prefix(parent, parentIdx + 1)), I(prefix(children[childrenIdx], childIdx + 1)), pivots, childrenIdx)
  {
    var child := children[childrenIdx];
    flushIterateCurLastLt(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
    flushIterateNextsNotInPrefixes(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
    StrictlySortedAugment(cur.keys, child.keys[childIdx]);
    BucketListItemFlushAddParentAndChildKey(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, child.keys[childIdx], parent.values[parentIdx], child.values[childIdx]);

    assert WFBucketAt(I(children[childrenIdx]), pivots, childrenIdx);
    Imaps(child, childIdx);
    assert child.keys[childIdx] in I(children[childrenIdx]);
    assert P.Route(pivots, child.keys[childIdx]) == childrenIdx;

    Iappend(cur, parent.keys[parentIdx], Merge(parent.values[parentIdx], children[childrenIdx].values[childIdx]));
    Iprefix_append(parent, parentIdx);
    Iprefix_append(child, childIdx);

    /*assert I(append(cur, parent.keys[parentIdx], Merge(parent.values[parentIdx], children[childrenIdx].values[childIdx])))
        == I(cur)[parent.keys[parentIdx] := Merge(parent.values[parentIdx], children[childrenIdx].values[childIdx])]
        == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx)[parent.keys[parentIdx] := Merge(parent.values[parentIdx], children[childrenIdx].values[childIdx])]
        == BucketListItemFlush(I(prefix(parent, parentIdx))[parent.keys[parentIdx] := parent.values[parentIdx]], I(prefix(children[childrenIdx], childIdx))[child.keys[childIdx] := child.values[childIdx]], pivots, childrenIdx)
        == BucketListItemFlush(I(prefix(parent, parentIdx + 1)), I(prefix(children[childrenIdx], childIdx + 1)), pivots, childrenIdx);*/
  }

  lemma flushIterateCurEqBucketListItemFlush(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<KMTable>, cur: KMTable)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  requires childrenIdx < |children|
  requires childIdx == |children[childrenIdx].keys|
  requires parentIdx < |parent.keys| ==> childrenIdx < |pivots| && lte(pivots[childrenIdx], parent.keys[parentIdx])
  ensures I(cur) == BucketListItemFlush(I(parent), I(children[childrenIdx]), pivots, childrenIdx)
  {
    forall key | P.Route(pivots, key) == childrenIdx
    ensures MapsAgreeOnKey(I(prefix(parent, parentIdx)), I(parent), key)
    {
      WFPrefix(parent, parentIdx);
      if (key in I(prefix(parent, parentIdx))) {
        var i := IndexOfKey(prefix(parent, parentIdx), key);
        Imaps(parent, i);
        Imaps(prefix(parent, parentIdx), i);
      } else if (key in I(parent)) {
        var i := IndexOfKey(parent, key);
        if (i < parentIdx) {
          Imaps(parent, i);
          Imaps(prefix(parent, parentIdx), i);
        } else {
          assert lt(parent.keys[i], pivots[childrenIdx]);
          assert lte(pivots[childrenIdx], parent.keys[parentIdx]);
          IsStrictlySortedImpliesLte(parent.keys, parentIdx, i);
          assert false;
        }
      }
    }
    BucketListItemFlushEq(I(prefix(parent, parentIdx)), I(parent), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx);
    assert prefix(children[childrenIdx], childIdx) == children[childrenIdx];
  }

  lemma flushIteratepivotLteChildKey0(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<KMTable>, cur: KMTable)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  ensures childrenIdx < |pivots| && |children[childrenIdx + 1].keys| > 0 ==> lte(pivots[childrenIdx], children[childrenIdx + 1].keys[0])
  {
    if childrenIdx < |pivots| && |children[childrenIdx + 1].keys| > 0 {
      Imaps(children[childrenIdx + 1], 0);
      assert P.Route(pivots, children[childrenIdx + 1].keys[0]) == childrenIdx + 1;
    }
  }

  lemma flushIterateIEmptyEqBucketListItemFlush(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<KMTable>, cur: KMTable)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  requires childrenIdx + 1 < |children| && parentIdx > 0 ==> lt(parent.keys[parentIdx - 1], pivots[childrenIdx])
  ensures childrenIdx + 1 < |children| ==>
         I(KMTable([],[]))
      == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx + 1], 0)), pivots, childrenIdx + 1)
  {
    reveal_I();
    forall key | key in I(prefix(parent, parentIdx))
    ensures P.Route(pivots, key) != childrenIdx + 1
    {
      var i := IndexOfKey(prefix(parent, parentIdx), key);
      IsStrictlySortedImpliesLte(parent.keys, i, parentIdx - 1);
    }
  }

  lemma flushIterateRes(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<KMTable>, cur: KMTable)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  ensures var f := flushIterate(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
      && (forall i | 0 <= i < |f| :: WF(f[i]))
      && ISeq(f) == BucketListFlush(I(parent), ISeq(children), pivots)
  decreases |children| - childrenIdx
  decreases |parent.keys| - parentIdx +
      (if childrenIdx < |children| then |children[childrenIdx].keys| - childIdx else 0)
  {
    if childrenIdx == |children| {
    } else {
      var child := children[childrenIdx];

      if parentIdx + 1 < |parent.keys| {
        IsStrictlySortedImpliesLt(parent.keys, parentIdx, parentIdx + 1);
      }
      if childrenIdx + 1 < |pivots| {
        IsStrictlySortedImpliesLt(pivots, childrenIdx, childrenIdx + 1);
      }
      if childIdx + 1 < |child.keys| {
        IsStrictlySortedImpliesLt(child.keys, childIdx, childIdx + 1);
      }
      if childIdx < |child.keys| {
        Imaps(child, childIdx);
        assert P.Route(pivots, child.keys[childIdx]) == childrenIdx;
      }

      if parentIdx == |parent.keys| {
        if childIdx == |child.keys| {
          flushIterateCurEqBucketListItemFlush(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
          flushIterateIEmptyEqBucketListItemFlush(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
          flushIteratepivotLteChildKey0(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
          flushIterateRes(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], KMTable([], []));
        //} else if |cur| == 0 {
        //  flushIterateRes(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [child], KMTable([], []));
        } else {
          flushIterateAppendChild(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
          flushIterateRes(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], child.values[childIdx]));
        }
      } else {
        if childIdx == |child.keys| {
          if childrenIdx == |children| - 1 {
            flushIterateAppendParent(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
            flushIterateRes(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.values[parentIdx]));
          } else {
            if lt(parent.keys[parentIdx], pivots[childrenIdx]) {
              flushIterateAppendParent(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
              flushIterateRes(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.values[parentIdx]));
            } else {
              flushIterateCurEqBucketListItemFlush(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
              flushIterateIEmptyEqBucketListItemFlush(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
              flushIteratepivotLteChildKey0(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
              flushIterateRes(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], KMTable([], []));
            }
          }
        } else {
          if child.keys[childIdx] == parent.keys[parentIdx] {
            var m := Merge(parent.values[parentIdx], child.values[childIdx]);
            if m == IdentityMessage() {
              flushIterateRes(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, cur);
            } else {
              flushIterateAppendParentAndChild(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
              flushIterateRes(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], m));
            }
          } else if lt(child.keys[childIdx], parent.keys[parentIdx]) {
            flushIterateAppendChild(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
            flushIterateRes(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], child.values[childIdx]));
          } else {
            flushIterateAppendParent(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
            flushIterateRes(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.values[parentIdx]));
          }
        }
      }
    }
  }

  lemma flushRes(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>)
  requires WF(parent)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires WFBucketList(ISeq(children), pivots)
  ensures var f := flush(parent, children, pivots);
      && (forall i | 0 <= i < |f| :: WF(f[i]))
      && ISeq(f) == BucketListFlush(I(parent), ISeq(children), pivots)
  {
    reveal_I();
    flushIterateRes(parent, children, pivots, 0, 0, 0, [], KMTable([], []));
  }

  method Flush(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>)
  returns (f : seq<KMTable>)
  requires WF(parent)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires WFBucketList(ISeq(children), pivots)
  requires |children| < 0x1_0000_0000_0000_0000
  requires forall i | 0 <= i < |children| :: |children[i].keys| + |parent.keys| < 0x8000_0000_0000_0000
  ensures forall i | 0 <= i < |f| :: WF(f[i])
  ensures ISeq(f) == BucketListFlush(I(parent), ISeq(children), pivots)
  ensures f == flush(parent, children, pivots)
  {
    assert |children[0].keys| + |parent.keys| < 0x8000_0000_0000_0000;

    var maxChildLen: uint64 := 0;
    var idx: uint64 := 0;
    while idx < |children| as uint64
    invariant 0 <= idx as int <= |children|
    invariant forall i | 0 <= i < idx as int :: |children[i].keys| <= maxChildLen as int
    invariant maxChildLen as int + |parent.keys| < 0x8000_0000_0000_0000
    {
      if |children[idx].keys| as uint64 > maxChildLen {
        maxChildLen := |children[idx].keys| as uint64;
      }
      idx := idx + 1;
    }

    var parentIdx: uint64 := 0;
    var childrenIdx: uint64 := 0;
    var childIdx: uint64 := 0;
    var acc := [];
    var cur_keys := new Key[maxChildLen + |parent.keys| as uint64];

    var defaultMessage := IdentityMessage();
    var cur_values := new Message[maxChildLen + |parent.keys| as uint64]((i) => defaultMessage);

    var cur_idx: uint64 := 0;

    while childrenIdx < |children| as uint64
    invariant 0 <= parentIdx as int <= |parent.keys|
    invariant 0 <= childrenIdx as int <= |children|
    invariant (childrenIdx as int < |children| ==> 0 <= childIdx as int <= |children[childrenIdx].keys|)
    invariant 0 <= cur_idx
    invariant childrenIdx as int < |children| ==> cur_idx as int <= parentIdx as int + childIdx as int
    invariant childrenIdx as int == |children| ==> cur_idx == 0
    invariant flushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, KMTable(cur_keys[..cur_idx], cur_values[..cur_idx]))
        == flush(parent, children, pivots)
    decreases |children| - childrenIdx as int
    decreases |parent.keys| - parentIdx as int +
        (if childrenIdx as int < |children| then |children[childrenIdx].keys| - childIdx as int else 0)
    {
      var child := children[childrenIdx];
      if parentIdx == |parent.keys| as uint64 {
        if childIdx == |child.keys| as uint64 {
          childrenIdx := childrenIdx + 1;
          childIdx := 0;
          acc := acc + [KMTable(cur_keys[..cur_idx], cur_values[..cur_idx])];
          cur_idx := 0;
        } else {
          cur_keys[cur_idx] := child.keys[childIdx];
          cur_values[cur_idx] := child.values[childIdx];
          assert append(KMTable(cur_keys[..cur_idx], cur_values[..cur_idx]), child.keys[childIdx], child.values[childIdx]) == KMTable(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
          childIdx := childIdx + 1;
          cur_idx := cur_idx + 1;
        }
      } else {
        if childIdx == |child.keys| as uint64 {
          if childrenIdx == |children| as uint64 - 1 {
            cur_keys[cur_idx] := parent.keys[parentIdx];
            cur_values[cur_idx] := parent.values[parentIdx];
            assert append(KMTable(cur_keys[..cur_idx], cur_values[..cur_idx]), parent.keys[parentIdx], parent.values[parentIdx]) == KMTable(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
            parentIdx := parentIdx + 1;
            cur_idx := cur_idx + 1;
          } else {
            var c := cmp(parent.keys[parentIdx], pivots[childrenIdx]);
            if c < 0 {
              cur_keys[cur_idx] := parent.keys[parentIdx];
              cur_values[cur_idx] := parent.values[parentIdx];
              assert append(KMTable(cur_keys[..cur_idx], cur_values[..cur_idx]), parent.keys[parentIdx], parent.values[parentIdx]) == KMTable(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
              parentIdx := parentIdx + 1;
              cur_idx := cur_idx + 1;
            } else {
              acc := acc + [KMTable(cur_keys[..cur_idx], cur_values[..cur_idx])];
              childrenIdx := childrenIdx + 1;
              childIdx := 0;
              cur_idx := 0;
            }
          }
        } else {
          var c := cmp(child.keys[childIdx], parent.keys[parentIdx]);
          if c == 0 {
            var m := Merge(parent.values[parentIdx], child.values[childIdx]);
            if m == IdentityMessage() {
              parentIdx := parentIdx + 1;
              childIdx := childIdx + 1;
            } else {
              cur_keys[cur_idx] := parent.keys[parentIdx];
              cur_values[cur_idx] := m;
              assert append(KMTable(cur_keys[..cur_idx], cur_values[..cur_idx]), parent.keys[parentIdx], m) == KMTable(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
              cur_idx := cur_idx + 1;
              parentIdx := parentIdx + 1;
              childIdx := childIdx + 1;
            }
          } else if c < 0 {
            cur_keys[cur_idx] := child.keys[childIdx];
            cur_values[cur_idx] := child.values[childIdx];
            assert append(KMTable(cur_keys[..cur_idx], cur_values[..cur_idx]), child.keys[childIdx], child.values[childIdx]) == KMTable(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
            childIdx := childIdx + 1;
            cur_idx := cur_idx + 1;
          } else {
            cur_keys[cur_idx] := parent.keys[parentIdx];
            cur_values[cur_idx] := parent.values[parentIdx];
            assert append(KMTable(cur_keys[..cur_idx], cur_values[..cur_idx]), parent.keys[parentIdx], parent.values[parentIdx]) == KMTable(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
            parentIdx := parentIdx + 1;
            cur_idx := cur_idx + 1;
          }
        }
      }
    }

    flushRes(parent, children, pivots);
    return acc;
  }

  /////////////////////////
  //// Query
  /////////////////////////

  method Query(kmt: KMTable, key: Key) returns (m: Option<Message>)
  requires WF(kmt)
  requires |kmt.keys| < 0x8000_0000_0000_0000
  ensures m.None? ==> key !in I(kmt)
  ensures m.Some? ==> key in I(kmt) && I(kmt)[key] == m.value
  {
    var lo: uint64 := 0;
    var hi: uint64 := |kmt.keys| as uint64;

    while lo < hi
    invariant 0 <= lo as int <= |kmt.keys|
    invariant 0 <= hi as int <= |kmt.keys|
    invariant lo > 0 ==> lt(kmt.keys[lo-1], key)
    invariant hi as int < |kmt.keys| ==> lt(key, kmt.keys[hi])
    decreases hi as int - lo as int
    {
      var mid: uint64 := (lo + hi) / 2;
      var c := cmp(key, kmt.keys[mid]);
      if c == 0 {
        m := Some(kmt.values[mid]);
        Imaps(kmt, mid as int);
        return;
      } else if (c < 0) {
        hi := mid;
      } else {
        lo := mid + 1;
      }
    }

    if (key in I(kmt)) {
      ghost var j := IndexOfKey(kmt, key);
      if (lo > 0) { IsStrictlySortedImpliesLtIndices(kmt.keys, lo as int - 1, j as int); }
      if (hi as int < |kmt.keys|) { IsStrictlySortedImpliesLtIndices(kmt.keys, j as int, hi as int); }
    }

    m := None;
  }

  /////////////////////////
  //// Splitting
  /////////////////////////

  method ComputeCutoffPoint(kmt: KMTable, key: Key)
  returns (idx: uint64)
  requires WF(kmt)
  requires |kmt.keys| < 0x8000_0000_0000_0000
  ensures 0 <= idx as int <= |kmt.keys|
  ensures forall i | 0 <= i < idx as int :: lt(kmt.keys[i], key)
  ensures forall i | idx as int <= i as int < |kmt.keys| :: lte(key, kmt.keys[i])
  {
    var lo: uint64 := 0;
    var hi: uint64 := |kmt.keys| as uint64;

    while lo < hi
    invariant 0 <= lo as int <= |kmt.keys|
    invariant 0 <= hi as int <= |kmt.keys|
    invariant forall i | 0 <= i < lo as int :: lt(kmt.keys[i], key)
    invariant forall i | hi as int <= i < |kmt.keys| :: lte(key, kmt.keys[i])
    decreases hi as int - lo as int
    {
      reveal_IsStrictlySorted();

      var mid: uint64 := (lo + hi) / 2;
      var c := cmp(key, kmt.keys[mid]);
      if (c > 0) {
        lo := mid + 1;
      } else {
        hi := mid;
      }
    }

    idx := lo;
  }

  function splitLeft(kmt: KMTable, pivot: Key) : (left : KMTable)
  requires |kmt.keys| == |kmt.values|

  lemma splitLeftCorrect(kmt: KMTable, pivot: Key)
  requires WF(kmt)
  ensures var left := splitLeft(kmt, pivot);
    && WF(left)
    && I(left) == SplitBucketLeft(I(kmt), pivot)
    && left == splitLeft(kmt, pivot)

  method SplitLeft(kmt: KMTable, pivot: Key)
  returns (left: KMTable)
  requires WF(kmt)
  requires |kmt.keys| < 0x8000_0000_0000_0000
  ensures WF(left)
  ensures I(left) == SplitBucketLeft(I(kmt), pivot)
  ensures left == splitLeft(kmt, pivot)
  {
    var idx := ComputeCutoffPoint(kmt, pivot);
    left := KMTable(kmt.keys[..idx], kmt.values[..idx]);

    reveal_IsStrictlySorted();

    ghost var a := I(left);
    ghost var b := SplitBucketLeft(I(kmt), pivot);

    forall key | key in a
    ensures key in b
    ensures a[key] == b[key]
    {
      ghost var i := IndexOfKey(left, key);
      Imaps(left, i);
      Imaps(kmt, i);
    }

    forall key | key in b
    ensures key in a
    {
      ghost var i := IndexOfKey(kmt, key);
      Imaps(left, i);
      Imaps(kmt, i);
    }

    assert a == b;

    assume left == splitLeft(kmt, pivot);
  }

  function splitRight(kmt: KMTable, pivot: Key) : (right : KMTable)
  requires |kmt.keys| == |kmt.values|

  lemma splitRightCorrect(kmt: KMTable, pivot: Key)
  requires WF(kmt)
  ensures var right := splitRight(kmt, pivot);
    && WF(right)
    && I(right) == SplitBucketRight(I(kmt), pivot)
    && right == splitRight(kmt, pivot)

  method SplitRight(kmt: KMTable, pivot: Key)
  returns (right: KMTable)
  requires WF(kmt)
  requires |kmt.keys| < 0x8000_0000_0000_0000
  ensures WF(right)
  ensures I(right) == SplitBucketRight(I(kmt), pivot)
  ensures right == splitRight(kmt, pivot)
  {
    var idx := ComputeCutoffPoint(kmt, pivot);
    right := KMTable(kmt.keys[idx..], kmt.values[idx..]);

    reveal_IsStrictlySorted();

    ghost var a := I(right);
    ghost var b := SplitBucketRight(I(kmt), pivot);

    forall key | key in a
    ensures key in b
    ensures a[key] == b[key]
    {
      ghost var i := IndexOfKey(right, key);
      Imaps(right, i);
      Imaps(kmt, i + idx as int);
    }

    forall key | key in b
    ensures key in a
    {
      ghost var i := IndexOfKey(kmt, key);
      Imaps(right, i - idx as int);
      Imaps(kmt, i);
    }

    assert a == b;
    assume right == splitRight(kmt, pivot);
  }

  function splitKMTableInList(buckets: seq<KMTable>, slot: int, pivot: Key)
  : (buckets' : seq<KMTable>)
  requires forall i | 0 <= i < |buckets| :: WF(buckets[i])
  requires 0 <= slot < |buckets|
  ensures |buckets'| == |buckets| + 1

  lemma splitKMTableInListCorrect(buckets: seq<KMTable>, slot: int, pivot: Key)
  requires forall i | 0 <= i < |buckets| :: WF(buckets[i])
  requires 0 <= slot < |buckets|
  ensures var buckets' := splitKMTableInList(buckets, slot, pivot);
    && |buckets'| == |buckets| + 1
    && (forall i | 0 <= i < |buckets'| :: WF(buckets'[i]))
    && (ISeq(buckets') == SplitBucketInList(ISeq(buckets), slot, pivot))

  method SplitKMTableInList(buckets: seq<KMTable>, slot: int, pivot: Key)
  returns (buckets' : seq<KMTable>)
  requires forall i | 0 <= i < |buckets| :: WF(buckets[i])
  requires 0 <= slot < |buckets|
  requires |buckets[slot].keys| < 0x8000_0000_0000_0000
  ensures |buckets'| == |buckets| + 1
  ensures forall i | 0 <= i < |buckets'| :: WF(buckets'[i])
  ensures ISeq(buckets') == SplitBucketInList(ISeq(buckets), slot, pivot)
  ensures buckets' == splitKMTableInList(buckets, slot, pivot)
  {
    var l := SplitLeft(buckets[slot], pivot);
    var r := SplitRight(buckets[slot], pivot);
    buckets' := replace1with2(buckets, l, r, slot);
    reveal_SplitBucketInList();
    Ireplace1with2(buckets, l, r, slot);
    assume buckets' == splitKMTableInList(buckets, slot, pivot);
  }

  /////////////////////////
  //// Joining
  /////////////////////////

  function join(kmts: seq<KMTable>) : KMTable
  {
    if |kmts| == 0 then KMTable([], []) else (
      var j := join(DropLast(kmts));
      var l := Last(kmts);
      KMTable(j.keys + l.keys, j.values + l.values)
    )
  }

  function LenSum(kmts: seq<KMTable>, i: int) : int
  requires 0 <= i <= |kmts|
  {
    if i == 0 then 0 else LenSum(kmts, i-1) + |kmts[i-1].keys|
  }

  lemma LenSumPrefixLe(kmts: seq<KMTable>, i: int)
  requires 0 <= i <= |kmts|
  ensures LenSum(kmts, i) <= LenSum(kmts, |kmts|)

  decreases |kmts| - i
  {
    if (i < |kmts|) {
      LenSumPrefixLe(kmts, i+1);
    }
  }

  lemma joinEqJoinBucketList(kmts: seq<KMTable>, pivots: seq<Key>)
  requires forall i | 0 <= i < |kmts| :: WF(kmts[i])
  requires WFBucketList(ISeq(kmts), pivots)
  ensures WF(join(kmts))
  ensures I(join(kmts)) == JoinBucketList(ISeq(kmts))
  {
    assume false;
  }

  method {:fuel JoinBucketList,0} {:fuel WFBucketList,0}
  Join(kmts: seq<KMTable>, ghost pivots: seq<Key>)
  returns (kmt: KMTable)
  requires forall i | 0 <= i < |kmts| :: WF(kmts[i])
  requires WFBucketList(ISeq(kmts), pivots)
  requires |kmts| < 0x8000_0000
  requires forall i | 0 <= i < |kmts| :: |kmts[i].keys| < 0x1_0000_0000
  ensures WF(kmt)
  ensures I(kmt) == JoinBucketList(ISeq(kmts))
  ensures kmt == join(kmts)
  {
    var len: uint64 := 0;
    var i: uint64 := 0;
    while i < |kmts| as uint64
    invariant 0 <= i as int <= |kmts|
    invariant len as int == LenSum(kmts, i as int)
    invariant len <= i * 0x1_0000_0000
    {
      LenSumPrefixLe(kmts, i as int + 1);

      len := len + |kmts[i].keys| as uint64;
      i := i + 1;
    }

    assert kmts == kmts[..i];
    assert len as int == LenSum(kmts, |kmts|);
    var keys := new Key[len];
    var defaultMessage := IdentityMessage();
    var values := new Message[len]((i) => defaultMessage);

    var j: uint64 := 0;
    var pos: uint64 := 0;
    while j < |kmts| as uint64
    invariant 0 <= j as int <= |kmts|
    invariant pos as int == LenSum(kmts, j as int)
    invariant 0 <= LenSum(kmts, j as int) <= keys.Length
    invariant keys[..LenSum(kmts, j as int)] == join(kmts[..j]).keys
    invariant values[..LenSum(kmts, j as int)] == join(kmts[..j]).values
    {
      LenSumPrefixLe(kmts, j as int + 1);

      assert LenSum(kmts, j as int + 1)
          == LenSum(kmts, j as int) + |kmts[j].keys|
          == pos as int + |kmts[j].keys|;

      assert pos as int + |kmts[j].keys| <= keys.Length;
      Native.Arrays.CopySeqIntoArray(kmts[j].keys, 0, keys, pos, |kmts[j].keys| as uint64);
      Native.Arrays.CopySeqIntoArray(kmts[j].values, 0, values, pos, |kmts[j].values| as uint64);

      assert pos as int + |kmts[j].keys|
          == LenSum(kmts, j as int) + |kmts[j].keys|
          == LenSum(kmts, j as int + 1);

      assert DropLast(kmts[..j+1]) == kmts[..j];
      assert keys[..LenSum(kmts, j as int + 1)]
          == keys[..pos] + keys[pos .. LenSum(kmts, j as int + 1)]
          == join(kmts[..j]).keys + kmts[j].keys
          == join(kmts[..j+1]).keys;
      assert values[..LenSum(kmts, j as int + 1)]
          == join(kmts[..j+1]).values;

      pos := pos + |kmts[j].keys| as uint64;
      j := j + 1;
    }

    kmt := KMTable(keys[..], values[..]);

    assert keys[..] == keys[..LenSum(kmts, j as int)];
    assert values[..] == values[..LenSum(kmts, j as int)];
    assert kmts[..j] == kmts;
    joinEqJoinBucketList(kmts, pivots);
  }

  /////////////////////////
  //// Splitting
  /////////////////////////

  function method EmptySeq(n: int) : (s : seq<KMTable>)
  requires n >= 0
  ensures |s| == n
  ensures forall i | 0 <= i < n :: WF(s[i])
  ensures forall i | 0 <= i < n :: s[i] == KMTable([],[])
  {
    if n == 0 then [] else EmptySeq(n-1) + [KMTable([],[])]
  }

  function splitOnPivots(kmt: KMTable, pivots: seq<Key>)
  : (kmts : seq<KMTable>)
  requires WF(kmt)
  requires |pivots| < 0x7fff_ffff_ffff_ffff
  ensures forall i | 0 <= i < |kmts| :: WF(kmts[i])
  ensures ISeq(kmts) == SplitBucketOnPivots(I(kmt), pivots)
  ensures |kmts| == |pivots| + 1

  method SplitOnPivots(kmt: KMTable, pivots: seq<Key>)
  returns (kmts : seq<KMTable>)
  requires WF(kmt)
  requires P.WFPivots(pivots)
  requires |pivots| < 0x7fff_ffff_ffff_ffff
  requires |kmt.keys| < 0x8000_0000_0000_0000
  ensures forall i | 0 <= i < |kmts| :: WF(kmts[i])
  ensures ISeq(kmts) == SplitBucketOnPivots(I(kmt), pivots)
  ensures kmts == splitOnPivots(kmt, pivots)
  {
    reveal_I();
    kmts := Flush(kmt, EmptySeq(|pivots| + 1), pivots);

    forall key | key in I(kmt)
    ensures I(kmt)[key] != IdentityMessage()
    {
      var i := IndexOfKey(kmt, key);
      Imaps(kmt, i);
    }
    LemmaSplitBucketOnPivotsEqAddMessagesToBuckets(I(kmt), pivots, ISeq(EmptySeq(|pivots| + 1)));
    assume kmts == splitOnPivots(kmt, pivots);
  }

  method IsWF(kmt: KMTable) returns (b: bool)
  requires |kmt.keys| < 0x1_0000_0000_0000_0000
  requires |kmt.values| < 0x1_0000_0000_0000_0000
  requires IsStrictlySorted(kmt.keys)
  requires forall i | 0 <= i < |kmt.values| :: kmt.values[i] != IdentityMessage()
  ensures b == WF(kmt)
  {
    if |kmt.keys| as uint64 != |kmt.values| as uint64
    {
      return false;
    }

    /*
    reveal_IsStrictlySorted();

    var k: uint64 := 1;
    while k < |kmt.keys| as uint64
    invariant |kmt.keys| > 0 ==> 0 <= k as int <= |kmt.keys|
    invariant |kmt.keys| > 0 ==> forall i, j :: 0 <= i < j < k as int ==> lt(kmt.keys[i], kmt.keys[j])
    {
      var c := cmp(kmt.keys[k-1], kmt.keys[k]);
      if (c >= 0) {
        return false;
      }
      k := k + 1;
    }
    */

    return true;
  }

  /////////////////////////
  //// Misc utils
  /////////////////////////

  function method {:opaque} Empty() : (kmt : KMTable)
  ensures WF(kmt)
  ensures I(kmt) == map[]
  {
    reveal_I();
    KMTable([],[])
  }

  predicate method {:opaque} IsEmpty(kmt: KMTable)
  requires WF(kmt)
  ensures IsEmpty(kmt) == (I(kmt) == map[])
  {
    reveal_I();
    assert |kmt.keys| > 0 ==> Last(kmt.keys) in I(KMTable(DropLast(kmt.keys), DropLast(kmt.values)))[Last(kmt.keys) := Last(kmt.values)];
    var emp : Bucket := map[];
    assert |kmt.keys| > 0 ==> Last(kmt.keys) !in emp;
    assert |kmt.keys| > 0 ==> I(KMTable(DropLast(kmt.keys), DropLast(kmt.values)))[Last(kmt.keys) := Last(kmt.values)] != map[];

    |kmt.keys| == 0
  }

  lemma Islice(kmts: seq<KMTable>, a: int, b: int)
  requires 0 <= a <= b <= |kmts|
  requires forall i | 0 <= i < |kmts| :: WF(kmts[i])
  ensures forall i | 0 <= i < |kmts[a..b]| :: WF(kmts[a..b][i])
  ensures ISeq(kmts[a..b]) == ISeq(kmts)[a..b]
  {
    reveal_I();
    if b == |kmts| {
      if (a == b) {
      } else {
        Islice(DropLast(kmts), a, b - 1);
      }
    } else {
      Islice(DropLast(kmts), a, b);
    }
  }

  lemma Isuffix(kmts: seq<KMTable>, a: int)
  requires 0 <= a <= |kmts|
  requires forall i | 0 <= i < |kmts| :: WF(kmts[i])
  ensures forall i | 0 <= i < |kmts[a..]| :: WF(kmts[a..][i])
  ensures ISeq(kmts[a..]) == ISeq(kmts)[a..]
  {
    Islice(kmts, a, |kmts|);
  }

  lemma IPopFront(kmt: KMTable, kmts: seq<KMTable>)
  requires WF(kmt)
  requires forall i | 0 <= i < |kmts| :: WF(kmts[i])
  ensures ISeq([kmt] + kmts) == [I(kmt)] + ISeq(kmts)
  {
    if |kmts| == 0 {
    } else {
      IPopFront(kmt, DropLast(kmts));
    }
  }

  lemma IPopBack(kmts: seq<KMTable>, kmt: KMTable)
  requires WF(kmt)
  requires forall i | 0 <= i < |kmts| :: WF(kmts[i])
  ensures ISeq(kmts + [kmt]) == ISeq(kmts) + [I(kmt)]
  {
    reveal_ISeq();
  }

  lemma Ireplace1with2(kmts: seq<KMTable>, kmt1: KMTable, kmt2: KMTable, slot: int)
  requires WF(kmt1)
  requires WF(kmt2)
  requires 0 <= slot < |kmts|
  requires forall i | 0 <= i < |kmts| :: WF(kmts[i])
  ensures forall i | 0 <= i < |replace1with2(kmts, kmt1, kmt2, slot)| :: WF(replace1with2(kmts, kmt1, kmt2, slot)[i])
  ensures ISeq(replace1with2(kmts, kmt1, kmt2, slot)) == replace1with2(ISeq(kmts), I(kmt1), I(kmt2), slot)
  {
    forall i | 0 <= i < |replace1with2(kmts, kmt1, kmt2, slot)|
    ensures WF(replace1with2(kmts, kmt1, kmt2, slot)[i])
    {
      if i < slot {
        assert replace1with2(kmts, kmt1, kmt2, slot)[i] == kmts[i];
      }
      if i == slot {
        assert replace1with2(kmts, kmt1, kmt2, slot)[i] == kmt1;
      }
      if i == slot + 1 {
        assert replace1with2(kmts, kmt1, kmt2, slot)[i] == kmt2;
      }
      if i > slot + 1 {
        assert replace1with2(kmts, kmt1, kmt2, slot)[i] == kmts[i-1];
      }
    }

    if slot == |kmts|-1 {
    } else {
      Ireplace1with2(DropLast(kmts), kmt1, kmt2, slot);
    }

    reveal_replace1with2();
  }

  function kmtableOfSeq(s: seq<(Key, Message)>) : (kmt: KMTable)
  requires |s| < 0x1_0000_0000_0000_0000
  ensures WF(kmt)

  lemma kmtableOfSeqRes(s: seq<(Key, Message)>, m: map<Key, Message>)
  requires |s| < 0x1_0000_0000_0000_0000
  requires SortedSeqForMap(s, m)
  ensures WF(kmtableOfSeq(s))
  ensures I(kmtableOfSeq(s)) == m

  method KMTableOfSeq(s: seq<(Key, Message)>, ghost m: map<Key, Message>) returns (kmt: KMTable)
  requires SortedSeqForMap(s, m)
  requires |s| < 0x1_0000_0000_0000_0000
  ensures kmt == kmtableOfSeq(s)
  {
    assume false;

    var keys := new Key[|s| as uint64];
    var defaultMessage := IdentityMessage();
    var values := new Message[|s| as uint64]((i) => defaultMessage);

    var i := 0;
    while i < |s| as uint64
    {
      keys[i] := s[i].0;
      values[i] := s[i].1;
      i := i + 1;
    }

    kmt := KMTable(keys[..], values[..]);
  }

  /////////////////////////
  //// Weight stuff
  /////////////////////////

  function WeightKMTable(kmt: KMTable) : int
  {
    WeightKeySeq(kmt.keys) + WeightMessageSeq(kmt.values)
  }

  function WeightKMTableSeq(kmts: seq<KMTable>) : int
  {
    if |kmts| == 0 then 0 else WeightKMTableSeq(DropLast(kmts)) + WeightKMTable(Last(kmts))
  }

  method computeWeightKMTable(kmt: KMTable)
  returns (weight: uint64)
  requires WF(kmt)
  requires WeightKMTable(kmt) < 0x1_0000_0000_0000_0000
  ensures weight as int == WeightBucket(I(kmt))

  method computeWeightKMTableSeq(kmts: seq<KMTable>)
  returns (weight: uint64)
  requires forall i | 0 <= i < |kmts| :: WF(kmts[i])
  requires WeightKMTableSeq(kmts) < 0x1_0000_0000_0000_0000
  ensures weight as int == WeightBucketList(ISeq(kmts))

  lemma kmtableWeightEq(kmts: seq<KMTable>)
  requires forall i | 0 <= i < |kmts| :: WF(kmts[i])
  ensures WeightKMTableSeq(kmts) == WeightBucketList(ISeq(kmts))

  // This is far weaker than it could be, but it's probably good enough.
  // Weight is on the order of a few million, and I plan on using this lemma
  // to show that numbers fit within 64 bits.
  lemma lenKeysLeWeight(kmt: KMTable)
  requires WF(kmt)
  ensures |kmt.keys| <= WeightBucket(I(kmt))
}
