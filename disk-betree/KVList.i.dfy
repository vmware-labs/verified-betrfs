include "Message.i.dfy"
include "../lib/sequences.s.dfy"
include "../lib/Maps.s.dfy"
include "BucketsLib.i.dfy"
include "BucketWeights.i.dfy"
include "../lib/Marshalling/Seqs.i.dfy"

module KVList {
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

  datatype Kvl = Kvl(keys: seq<Key>, values: seq<Message>)

  predicate WF(kvl: Kvl) {
    && |kvl.keys| == |kvl.values|
    && IsStrictlySorted(kvl.keys)
    && (forall i | 0 <= i < |kvl.values| :: kvl.values[i] != IdentityMessage())
  }

  function {:opaque} I(kvl: Kvl) : Bucket
  requires |kvl.keys| == |kvl.values|
  decreases |kvl.keys|
  {
    if |kvl.keys| == 0 then map[] else (
      I(Kvl(DropLast(kvl.keys), DropLast(kvl.values)))[Last(kvl.keys) := Last(kvl.values)]
    )
  }

  function {:opaque} ISeq(kvls: seq<Kvl>) : (s : seq<Bucket>)
  requires forall i | 0 <= i < |kvls| :: |kvls[i].keys| == |kvls[i].values|
  ensures |s| == |kvls|
  ensures forall i | 0 <= i < |kvls| :: s[i] == I(kvls[i])
  {
    if |kvls| == 0 then [] else ISeq(DropLast(kvls)) + [I(Last(kvls))]
  }

  function prefix(kvl: Kvl, i: int) : Kvl
  requires 0 <= i <= |kvl.keys|
  requires 0 <= i <= |kvl.values|
  {
    Kvl(kvl.keys[..i], kvl.values[..i]) 
  }

  lemma WFPrefix(kvl: Kvl, i: int)
  requires WF(kvl)
  requires 0 <= i <= |kvl.keys|
  ensures WF(prefix(kvl, i))
  {
    reveal_IsStrictlySorted();
  }

  lemma IndexOfKey(kvl: Kvl, key: Key) returns (i : int)
  requires |kvl.keys| == |kvl.values|
  requires key in I(kvl)
  ensures 0 <= i < |kvl.keys|
  ensures kvl.keys[i] == key
  decreases |kvl.keys|
  {
    reveal_I();
    if key == Last(kvl.keys) {
      i := |kvl.keys| - 1;
    } else {
      i := IndexOfKey(Kvl(DropLast(kvl.keys), DropLast(kvl.values)), key);
    }
  }

  lemma Imaps(kvl: Kvl, i: int)
  requires WF(kvl)
  requires 0 <= i < |kvl.keys|
  ensures MapsTo(I(kvl), kvl.keys[i], kvl.values[i])
  decreases |kvl.keys|
  {
    reveal_I();
    if (i == |kvl.keys| - 1) {
    } else {
      reveal_IsStrictlySorted();
      Imaps(Kvl(DropLast(kvl.keys), DropLast(kvl.values)), i);
      assert kvl.keys[|kvl.keys| - 1] != kvl.keys[i];
    }
  }

  lemma WFImpliesWFBucket(kvl: Kvl)
  requires WF(kvl)
  ensures WFBucket(I(kvl))
  decreases |kvl.keys|
  {
    reveal_I();
    reveal_WFBucket();
    if |kvl.keys| == 0 {
    } else {
      ghost var km' := Kvl(DropLast(kvl.keys), DropLast(kvl.values));
      WFPrefix(kvl, |kvl.keys| - 1);
      assert WF(km');
      WFImpliesWFBucket(km');
    }
  }

  /////////////////////////
  //// Flush
  /////////////////////////

  function append(kvl: Kvl, key: Key, value: Message) : Kvl
  {
    Kvl(kvl.keys + [key], kvl.values + [value])
  }

  lemma Iappend(kvl: Kvl, key: Key, value: Message)
  requires |kvl.keys| == |kvl.values|
  ensures I(append(kvl, key, value)) == I(kvl)[key := value]
  {
    reveal_I();
  }

  lemma Iprefix_append(kvl: Kvl, i: int)
  requires |kvl.keys| == |kvl.values|
  requires 0 <= i < |kvl.keys|
  ensures I(prefix(kvl, i + 1)) == I(prefix(kvl, i))[kvl.keys[i] := kvl.values[i]]
  {
    assert prefix(kvl, i + 1) == append(prefix(kvl, i), kvl.keys[i], kvl.values[i]);
    Iappend(prefix(kvl, i), kvl.keys[i], kvl.values[i]);
  }

  function flushIterate(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl) : seq<Kvl>
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
          flushIterate(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], Kvl([], []))
        //) else if |cur.keys| == 0 then (
        //  flushIterate(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [child], Kvl([], []))
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
              flushIterate(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], Kvl([], []))
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

  function flush(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>) : seq<Kvl>
  requires WF(parent)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires |pivots| + 1 == |children|
  {
    flushIterate(parent, children, pivots, 0, 0, 0, [], Kvl([], []))
  }

  predicate flushIterateInv(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
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

  lemma flushIterateCurLastLt(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
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

  lemma flushIterateNextsNotInPrefixes(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
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

  lemma flushIterateAppendParent(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
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

  lemma flushIterateAppendChild(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
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
  flushIterateAppendParentAndChild(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
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

  lemma flushIterateCurEqBucketListItemFlush(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
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

  lemma flushIteratepivotLteChildKey0(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  ensures childrenIdx < |pivots| && |children[childrenIdx + 1].keys| > 0 ==> lte(pivots[childrenIdx], children[childrenIdx + 1].keys[0])
  {
    if childrenIdx < |pivots| && |children[childrenIdx + 1].keys| > 0 {
      Imaps(children[childrenIdx + 1], 0);
      assert P.Route(pivots, children[childrenIdx + 1].keys[0]) == childrenIdx + 1;
    }
  }

  lemma flushIterateIEmptyEqBucketListItemFlush(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  requires childrenIdx + 1 < |children| && parentIdx > 0 ==> lt(parent.keys[parentIdx - 1], pivots[childrenIdx])
  ensures childrenIdx + 1 < |children| ==>
         I(Kvl([],[]))
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

  lemma flushIterateRes(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
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
          flushIterateRes(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], Kvl([], []));
        //} else if |cur| == 0 {
        //  flushIterateRes(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [child], Kvl([], []));
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
              flushIterateRes(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], Kvl([], []));
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

  lemma flushRes(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>)
  requires WF(parent)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires WFBucketList(ISeq(children), pivots)
  ensures var f := flush(parent, children, pivots);
      && (forall i | 0 <= i < |f| :: WF(f[i]))
      && ISeq(f) == BucketListFlush(I(parent), ISeq(children), pivots)
  {
    reveal_I();
    flushIterateRes(parent, children, pivots, 0, 0, 0, [], Kvl([], []));
  }

  method Flush(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>)
  returns (f : seq<Kvl>)
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

    var cur_values := new Message[maxChildLen + |parent.keys| as uint64];

    var cur_idx: uint64 := 0;

    while childrenIdx < |children| as uint64
    invariant 0 <= parentIdx as int <= |parent.keys|
    invariant 0 <= childrenIdx as int <= |children|
    invariant (childrenIdx as int < |children| ==> 0 <= childIdx as int <= |children[childrenIdx].keys|)
    invariant 0 <= cur_idx
    invariant childrenIdx as int < |children| ==> cur_idx as int <= parentIdx as int + childIdx as int
    invariant childrenIdx as int == |children| ==> cur_idx == 0
    invariant flushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]))
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
          acc := acc + [Kvl(cur_keys[..cur_idx], cur_values[..cur_idx])];
          cur_idx := 0;
        } else {
          cur_keys[cur_idx] := child.keys[childIdx];
          cur_values[cur_idx] := child.values[childIdx];
          assert append(Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), child.keys[childIdx], child.values[childIdx]) == Kvl(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
          childIdx := childIdx + 1;
          cur_idx := cur_idx + 1;
        }
      } else {
        if childIdx == |child.keys| as uint64 {
          if childrenIdx == |children| as uint64 - 1 {
            cur_keys[cur_idx] := parent.keys[parentIdx];
            cur_values[cur_idx] := parent.values[parentIdx];
            assert append(Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), parent.keys[parentIdx], parent.values[parentIdx]) == Kvl(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
            parentIdx := parentIdx + 1;
            cur_idx := cur_idx + 1;
          } else {
            var c := cmp(parent.keys[parentIdx], pivots[childrenIdx]);
            if c < 0 {
              cur_keys[cur_idx] := parent.keys[parentIdx];
              cur_values[cur_idx] := parent.values[parentIdx];
              assert append(Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), parent.keys[parentIdx], parent.values[parentIdx]) == Kvl(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
              parentIdx := parentIdx + 1;
              cur_idx := cur_idx + 1;
            } else {
              acc := acc + [Kvl(cur_keys[..cur_idx], cur_values[..cur_idx])];
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
              assert append(Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), parent.keys[parentIdx], m) == Kvl(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
              cur_idx := cur_idx + 1;
              parentIdx := parentIdx + 1;
              childIdx := childIdx + 1;
            }
          } else if c < 0 {
            cur_keys[cur_idx] := child.keys[childIdx];
            cur_values[cur_idx] := child.values[childIdx];
            assert append(Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), child.keys[childIdx], child.values[childIdx]) == Kvl(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
            childIdx := childIdx + 1;
            cur_idx := cur_idx + 1;
          } else {
            cur_keys[cur_idx] := parent.keys[parentIdx];
            cur_values[cur_idx] := parent.values[parentIdx];
            assert append(Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), parent.keys[parentIdx], parent.values[parentIdx]) == Kvl(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
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

  method Query(kvl: Kvl, key: Key) returns (m: Option<Message>)
  requires WF(kvl)
  requires |kvl.keys| < 0x8000_0000_0000_0000
  ensures m.None? ==> key !in I(kvl)
  ensures m.Some? ==> key in I(kvl) && I(kvl)[key] == m.value
  {
    var lo: uint64 := 0;
    var hi: uint64 := |kvl.keys| as uint64;

    while lo < hi
    invariant 0 <= lo as int <= |kvl.keys|
    invariant 0 <= hi as int <= |kvl.keys|
    invariant lo > 0 ==> lt(kvl.keys[lo-1], key)
    invariant hi as int < |kvl.keys| ==> lt(key, kvl.keys[hi])
    decreases hi as int - lo as int
    {
      var mid: uint64 := (lo + hi) / 2;
      var c := cmp(key, kvl.keys[mid]);
      if c == 0 {
        m := Some(kvl.values[mid]);
        Imaps(kvl, mid as int);
        return;
      } else if (c < 0) {
        hi := mid;
      } else {
        lo := mid + 1;
      }
    }

    if (key in I(kvl)) {
      ghost var j := IndexOfKey(kvl, key);
      if (lo > 0) { IsStrictlySortedImpliesLtIndices(kvl.keys, lo as int - 1, j as int); }
      if (hi as int < |kvl.keys|) { IsStrictlySortedImpliesLtIndices(kvl.keys, j as int, hi as int); }
    }

    m := None;
  }

  /////////////////////////
  //// Splitting
  /////////////////////////

  method ComputeCutoffPoint(kvl: Kvl, key: Key)
  returns (idx: uint64)
  requires WF(kvl)
  requires |kvl.keys| < 0x8000_0000_0000_0000
  ensures 0 <= idx as int <= |kvl.keys|
  ensures forall i | 0 <= i < idx as int :: lt(kvl.keys[i], key)
  ensures forall i | idx as int <= i as int < |kvl.keys| :: lte(key, kvl.keys[i])
  {
    var lo: uint64 := 0;
    var hi: uint64 := |kvl.keys| as uint64;

    while lo < hi
    invariant 0 <= lo as int <= |kvl.keys|
    invariant 0 <= hi as int <= |kvl.keys|
    invariant forall i | 0 <= i < lo as int :: lt(kvl.keys[i], key)
    invariant forall i | hi as int <= i < |kvl.keys| :: lte(key, kvl.keys[i])
    decreases hi as int - lo as int
    {
      reveal_IsStrictlySorted();

      var mid: uint64 := (lo + hi) / 2;
      var c := cmp(key, kvl.keys[mid]);
      if (c > 0) {
        lo := mid + 1;
      } else {
        hi := mid;
      }
    }

    idx := lo;
  }

  method SplitLeft(kvl: Kvl, pivot: Key)
  returns (left: Kvl)
  requires WF(kvl)
  requires |kvl.keys| < 0x8000_0000_0000_0000
  ensures WF(left)
  ensures I(left) == SplitBucketLeft(I(kvl), pivot)
  {
    var idx := ComputeCutoffPoint(kvl, pivot);
    left := Kvl(kvl.keys[..idx], kvl.values[..idx]);

    reveal_IsStrictlySorted();

    ghost var a := I(left);
    ghost var b := SplitBucketLeft(I(kvl), pivot);

    forall key | key in a
    ensures key in b
    ensures a[key] == b[key]
    {
      ghost var i := IndexOfKey(left, key);
      Imaps(left, i);
      Imaps(kvl, i);
    }

    forall key | key in b
    ensures key in a
    {
      ghost var i := IndexOfKey(kvl, key);
      Imaps(left, i);
      Imaps(kvl, i);
    }

    assert a == b;
  }

  method SplitRight(kvl: Kvl, pivot: Key)
  returns (right: Kvl)
  requires WF(kvl)
  requires |kvl.keys| < 0x8000_0000_0000_0000
  ensures WF(right)
  ensures I(right) == SplitBucketRight(I(kvl), pivot)
  {
    var idx := ComputeCutoffPoint(kvl, pivot);
    right := Kvl(kvl.keys[idx..], kvl.values[idx..]);

    reveal_IsStrictlySorted();

    ghost var a := I(right);
    ghost var b := SplitBucketRight(I(kvl), pivot);

    forall key | key in a
    ensures key in b
    ensures a[key] == b[key]
    {
      ghost var i := IndexOfKey(right, key);
      Imaps(right, i);
      Imaps(kvl, i + idx as int);
    }

    forall key | key in b
    ensures key in a
    {
      ghost var i := IndexOfKey(kvl, key);
      Imaps(right, i - idx as int);
      Imaps(kvl, i);
    }

    assert a == b;
  }

  /*function splitKvlInList(buckets: seq<Kvl>, slot: int, pivot: Key)
  : (buckets' : seq<Kvl>)
  requires forall i | 0 <= i < |buckets| :: WF(buckets[i])
  requires 0 <= slot < |buckets|
  ensures |buckets'| == |buckets| + 1

  lemma splitKvlInListCorrect(buckets: seq<Kvl>, slot: int, pivot: Key)
  requires forall i | 0 <= i < |buckets| :: WF(buckets[i])
  requires 0 <= slot < |buckets|
  ensures var buckets' := splitKvlInList(buckets, slot, pivot);
    && |buckets'| == |buckets| + 1
    && (forall i | 0 <= i < |buckets'| :: WF(buckets'[i]))
    && (ISeq(buckets') == SplitBucketInList(ISeq(buckets), slot, pivot))

  method SplitKvlInList(buckets: seq<Kvl>, slot: int, pivot: Key)
  returns (buckets' : seq<Kvl>)
  requires forall i | 0 <= i < |buckets| :: WF(buckets[i])
  requires 0 <= slot < |buckets|
  requires |buckets[slot].keys| < 0x8000_0000_0000_0000
  ensures |buckets'| == |buckets| + 1
  ensures forall i | 0 <= i < |buckets'| :: WF(buckets'[i])
  ensures ISeq(buckets') == SplitBucketInList(ISeq(buckets), slot, pivot)
  ensures buckets' == splitKvlInList(buckets, slot, pivot)
  {
    var l := SplitLeft(buckets[slot], pivot);
    var r := SplitRight(buckets[slot], pivot);
    buckets' := replace1with2(buckets, l, r, slot);
    reveal_SplitBucketInList();
    Ireplace1with2(buckets, l, r, slot);
    assume buckets' == splitKvlInList(buckets, slot, pivot);
  }*/

  /////////////////////////
  //// Joining
  /////////////////////////

  /*function join(kvls: seq<Kvl>) : Kvl
  {
    if |kvls| == 0 then Kvl([], []) else (
      var j := join(DropLast(kvls));
      var l := Last(kvls);
      Kvl(j.keys + l.keys, j.values + l.values)
    )
  }

  function LenSum(kvls: seq<Kvl>, i: int) : int
  requires 0 <= i <= |kvls|
  {
    if i == 0 then 0 else LenSum(kvls, i-1) + |kvls[i-1].keys|
  }

  lemma LenSumPrefixLe(kvls: seq<Kvl>, i: int)
  requires 0 <= i <= |kvls|
  ensures LenSum(kvls, i) <= LenSum(kvls, |kvls|)

  decreases |kvls| - i
  {
    if (i < |kvls|) {
      LenSumPrefixLe(kvls, i+1);
    }
  }

  lemma joinEqJoinBucketList(kvls: seq<Kvl>, pivots: seq<Key>)
  requires forall i | 0 <= i < |kvls| :: WF(kvls[i])
  requires WFBucketList(ISeq(kvls), pivots)
  ensures WF(join(kvls))
  ensures I(join(kvls)) == JoinBucketList(ISeq(kvls))
  {
    assume false;
  }

  method {:fuel JoinBucketList,0} {:fuel WFBucketList,0}
  Join(kvls: seq<Kvl>, ghost pivots: seq<Key>)
  returns (kvl: Kvl)
  requires forall i | 0 <= i < |kvls| :: WF(kvls[i])
  requires WFBucketList(ISeq(kvls), pivots)
  requires |kvls| < 0x8000_0000
  requires forall i | 0 <= i < |kvls| :: |kvls[i].keys| < 0x1_0000_0000
  ensures WF(kvl)
  ensures I(kvl) == JoinBucketList(ISeq(kvls))
  ensures kvl == join(kvls)
  {
    var len: uint64 := 0;
    var i: uint64 := 0;
    while i < |kvls| as uint64
    invariant 0 <= i as int <= |kvls|
    invariant len as int == LenSum(kvls, i as int)
    invariant len <= i * 0x1_0000_0000
    {
      LenSumPrefixLe(kvls, i as int + 1);

      len := len + |kvls[i].keys| as uint64;
      i := i + 1;
    }

    assert kvls == kvls[..i];
    assert len as int == LenSum(kvls, |kvls|);
    var keys := new Key[len];
    var values := new Message[len];

    var j: uint64 := 0;
    var pos: uint64 := 0;
    while j < |kvls| as uint64
    invariant 0 <= j as int <= |kvls|
    invariant pos as int == LenSum(kvls, j as int)
    invariant 0 <= LenSum(kvls, j as int) <= keys.Length
    invariant keys[..LenSum(kvls, j as int)] == join(kvls[..j]).keys
    invariant values[..LenSum(kvls, j as int)] == join(kvls[..j]).values
    {
      LenSumPrefixLe(kvls, j as int + 1);

      assert LenSum(kvls, j as int + 1)
          == LenSum(kvls, j as int) + |kvls[j].keys|
          == pos as int + |kvls[j].keys|;

      assert pos as int + |kvls[j].keys| <= keys.Length;
      Native.Arrays.CopySeqIntoArray(kvls[j].keys, 0, keys, pos, |kvls[j].keys| as uint64);
      Native.Arrays.CopySeqIntoArray(kvls[j].values, 0, values, pos, |kvls[j].values| as uint64);

      assert pos as int + |kvls[j].keys|
          == LenSum(kvls, j as int) + |kvls[j].keys|
          == LenSum(kvls, j as int + 1);

      assert DropLast(kvls[..j+1]) == kvls[..j];
      assert keys[..LenSum(kvls, j as int + 1)]
          == keys[..pos] + keys[pos .. LenSum(kvls, j as int + 1)]
          == join(kvls[..j]).keys + kvls[j].keys
          == join(kvls[..j+1]).keys;
      assert values[..LenSum(kvls, j as int + 1)]
          == join(kvls[..j+1]).values;

      pos := pos + |kvls[j].keys| as uint64;
      j := j + 1;
    }

    kvl := Kvl(keys[..], values[..]);

    assert keys[..] == keys[..LenSum(kvls, j as int)];
    assert values[..] == values[..LenSum(kvls, j as int)];
    assert kvls[..j] == kvls;
    joinEqJoinBucketList(kvls, pivots);
  }*/

  /////////////////////////
  //// Splitting
  /////////////////////////

  function method EmptySeq(n: int) : (s : seq<Kvl>)
  requires n >= 0
  ensures |s| == n
  ensures forall i | 0 <= i < n :: WF(s[i])
  ensures forall i | 0 <= i < n :: s[i] == Kvl([],[])
  {
    if n == 0 then [] else EmptySeq(n-1) + [Kvl([],[])]
  }

  /*function splitOnPivots(kvl: Kvl, pivots: seq<Key>)
  : (kvls : seq<Kvl>)
  requires WF(kvl)
  requires |pivots| < 0x7fff_ffff_ffff_ffff
  ensures forall i | 0 <= i < |kvls| :: WF(kvls[i])
  ensures ISeq(kvls) == SplitBucketOnPivots(I(kvl), pivots)
  ensures |kvls| == |pivots| + 1

  method SplitOnPivots(kvl: Kvl, pivots: seq<Key>)
  returns (kvls : seq<Kvl>)
  requires WF(kvl)
  requires P.WFPivots(pivots)
  requires |pivots| < 0x7fff_ffff_ffff_ffff
  requires |kvl.keys| < 0x8000_0000_0000_0000
  ensures forall i | 0 <= i < |kvls| :: WF(kvls[i])
  ensures ISeq(kvls) == SplitBucketOnPivots(I(kvl), pivots)
  ensures kvls == splitOnPivots(kvl, pivots)
  {
    reveal_I();
    kvls := Flush(kvl, EmptySeq(|pivots| + 1), pivots);

    forall key | key in I(kvl)
    ensures I(kvl)[key] != IdentityMessage()
    {
      var i := IndexOfKey(kvl, key);
      Imaps(kvl, i);
    }
    LemmaSplitBucketOnPivotsEqAddMessagesToBuckets(I(kvl), pivots, ISeq(EmptySeq(|pivots| + 1)));
    assume kvls == splitOnPivots(kvl, pivots);
  }*/

  method IsWF(kvl: Kvl) returns (b: bool)
  requires |kvl.keys| < 0x1_0000_0000_0000_0000
  requires |kvl.values| < 0x1_0000_0000_0000_0000
  requires IsStrictlySorted(kvl.keys)
  requires forall i | 0 <= i < |kvl.values| :: kvl.values[i] != IdentityMessage()
  ensures b == WF(kvl)
  {
    if |kvl.keys| as uint64 != |kvl.values| as uint64
    {
      return false;
    }

    /*
    reveal_IsStrictlySorted();

    var k: uint64 := 1;
    while k < |kvl.keys| as uint64
    invariant |kvl.keys| > 0 ==> 0 <= k as int <= |kvl.keys|
    invariant |kvl.keys| > 0 ==> forall i, j :: 0 <= i < j < k as int ==> lt(kvl.keys[i], kvl.keys[j])
    {
      var c := cmp(kvl.keys[k-1], kvl.keys[k]);
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

  function method {:opaque} Empty() : (kvl : Kvl)
  ensures WF(kvl)
  ensures I(kvl) == map[]
  {
    reveal_I();
    Kvl([],[])
  }

  predicate method {:opaque} IsEmpty(kvl: Kvl)
  requires WF(kvl)
  ensures IsEmpty(kvl) == (I(kvl) == map[])
  {
    reveal_I();
    assert |kvl.keys| > 0 ==> Last(kvl.keys) in I(Kvl(DropLast(kvl.keys), DropLast(kvl.values)))[Last(kvl.keys) := Last(kvl.values)];
    var emp : Bucket := map[];
    assert |kvl.keys| > 0 ==> Last(kvl.keys) !in emp;
    assert |kvl.keys| > 0 ==> I(Kvl(DropLast(kvl.keys), DropLast(kvl.values)))[Last(kvl.keys) := Last(kvl.values)] != map[];

    |kvl.keys| == 0
  }

  lemma Islice(kvls: seq<Kvl>, a: int, b: int)
  requires 0 <= a <= b <= |kvls|
  requires forall i | 0 <= i < |kvls| :: WF(kvls[i])
  ensures forall i | 0 <= i < |kvls[a..b]| :: WF(kvls[a..b][i])
  ensures ISeq(kvls[a..b]) == ISeq(kvls)[a..b]
  {
    reveal_I();
    if b == |kvls| {
      if (a == b) {
      } else {
        Islice(DropLast(kvls), a, b - 1);
      }
    } else {
      Islice(DropLast(kvls), a, b);
    }
  }

  lemma Isuffix(kvls: seq<Kvl>, a: int)
  requires 0 <= a <= |kvls|
  requires forall i | 0 <= i < |kvls| :: WF(kvls[i])
  ensures forall i | 0 <= i < |kvls[a..]| :: WF(kvls[a..][i])
  ensures ISeq(kvls[a..]) == ISeq(kvls)[a..]
  {
    Islice(kvls, a, |kvls|);
  }

  lemma IPopFront(kvl: Kvl, kvls: seq<Kvl>)
  requires WF(kvl)
  requires forall i | 0 <= i < |kvls| :: WF(kvls[i])
  ensures ISeq([kvl] + kvls) == [I(kvl)] + ISeq(kvls)
  {
    if |kvls| == 0 {
    } else {
      IPopFront(kvl, DropLast(kvls));
    }
  }

  lemma IPopBack(kvls: seq<Kvl>, kvl: Kvl)
  requires WF(kvl)
  requires forall i | 0 <= i < |kvls| :: WF(kvls[i])
  ensures ISeq(kvls + [kvl]) == ISeq(kvls) + [I(kvl)]
  {
    reveal_ISeq();
  }

  lemma Ireplace1with2(kvls: seq<Kvl>, kvl1: Kvl, kvl2: Kvl, slot: int)
  requires WF(kvl1)
  requires WF(kvl2)
  requires 0 <= slot < |kvls|
  requires forall i | 0 <= i < |kvls| :: WF(kvls[i])
  ensures forall i | 0 <= i < |replace1with2(kvls, kvl1, kvl2, slot)| :: WF(replace1with2(kvls, kvl1, kvl2, slot)[i])
  ensures ISeq(replace1with2(kvls, kvl1, kvl2, slot)) == replace1with2(ISeq(kvls), I(kvl1), I(kvl2), slot)
  {
    forall i | 0 <= i < |replace1with2(kvls, kvl1, kvl2, slot)|
    ensures WF(replace1with2(kvls, kvl1, kvl2, slot)[i])
    {
      if i < slot {
        assert replace1with2(kvls, kvl1, kvl2, slot)[i] == kvls[i];
      }
      if i == slot {
        assert replace1with2(kvls, kvl1, kvl2, slot)[i] == kvl1;
      }
      if i == slot + 1 {
        assert replace1with2(kvls, kvl1, kvl2, slot)[i] == kvl2;
      }
      if i > slot + 1 {
        assert replace1with2(kvls, kvl1, kvl2, slot)[i] == kvls[i-1];
      }
    }

    if slot == |kvls|-1 {
    } else {
      Ireplace1with2(DropLast(kvls), kvl1, kvl2, slot);
    }

    reveal_replace1with2();
  }

  function kvlOfSeq(s: seq<(Key, Message)>) : (kvl: Kvl)
  requires |s| < 0x1_0000_0000_0000_0000
  ensures WF(kvl)

  lemma kvlOfSeqRes(s: seq<(Key, Message)>, m: map<Key, Message>)
  requires |s| < 0x1_0000_0000_0000_0000
  requires SortedSeqForMap(s, m)
  ensures WF(kvlOfSeq(s))
  ensures I(kvlOfSeq(s)) == m

  method KvlOfSeq(s: seq<(Key, Message)>, ghost m: map<Key, Message>) returns (kvl: Kvl)
  requires SortedSeqForMap(s, m)
  requires |s| < 0x1_0000_0000_0000_0000
  ensures kvl == kvlOfSeq(s)
  {
    assume false;

    var keys := new Key[|s| as uint64];
    var values := new Message[|s| as uint64];

    var i := 0;
    while i < |s| as uint64
    {
      keys[i] := s[i].0;
      values[i] := s[i].1;
      i := i + 1;
    }

    kvl := Kvl(keys[..], values[..]);
  }

  /////////////////////////
  //// Weight stuff
  /////////////////////////

  function WeightKvl(kvl: Kvl) : int
  {
    WeightKeySeq(kvl.keys) + WeightMessageSeq(kvl.values)
  }

  function WeightKvlSeq(kvls: seq<Kvl>) : int
  {
    if |kvls| == 0 then 0 else WeightKvlSeq(DropLast(kvls)) + WeightKvl(Last(kvls))
  }

  lemma kvlWeightEq(kvl: Kvl)
  requires WF(kvl)
  ensures WeightKvl(kvl) == WeightBucket(I(kvl))
  decreases |kvl.keys|
  {
    reveal_I();
    if |kvl.keys| == 0 {
      WeightBucketEmpty();
    } else {
      WFPrefix(kvl, |kvl.keys| - 1);
      kvlWeightEq(Kvl(DropLast(kvl.keys), DropLast(kvl.values)));
      if Last(kvl.keys) in I(Kvl(DropLast(kvl.keys), DropLast(kvl.values))) {
        var i := IndexOfKey(Kvl(DropLast(kvl.keys), DropLast(kvl.values)), Last(kvl.keys));
        reveal_IsStrictlySorted();
      }
      WeightBucketInduct(I(Kvl(DropLast(kvl.keys), DropLast(kvl.values))), Last(kvl.keys), Last(kvl.values));
      assert WeightKvl(kvl)
          == WeightKvl(Kvl(DropLast(kvl.keys), DropLast(kvl.values)))
              + WeightKey(Last(kvl.keys)) + WeightMessage(Last(kvl.values))
          == WeightBucket(I(Kvl(DropLast(kvl.keys), DropLast(kvl.values))))
              + WeightKey(Last(kvl.keys)) + WeightMessage(Last(kvl.values));
    }
  }

  lemma kvlWeightPrefixLe(kvl: Kvl, j: int)
  requires WF(kvl)
  requires 0 <= j <= |kvl.keys|
  ensures WeightKvl(prefix(kvl, j)) <= WeightKvl(kvl);
  decreases |kvl.keys|
  {
    if j == |kvl.keys| {
      assert prefix(kvl, j) == kvl;
    } else {
      WFPrefix(kvl, |kvl.keys| - 1);
      kvlWeightPrefixLe(Kvl(DropLast(kvl.keys), DropLast(kvl.values)), j);
      assert prefix(kvl, j) == prefix(Kvl(DropLast(kvl.keys), DropLast(kvl.values)), j);
      assert WeightKvl(prefix(kvl, j))
          == WeightKvl(prefix(Kvl(DropLast(kvl.keys), DropLast(kvl.values)), j))
          <= WeightKvl(Kvl(DropLast(kvl.keys), DropLast(kvl.values)))
          <= WeightKvl(kvl);
    }
  }

  lemma lenKeysLeWeightOver8(kvl: Kvl)
  requires WF(kvl)
  ensures 8*|kvl.keys| <= WeightBucket(I(kvl))
  decreases |kvl.keys|
  {
    if |kvl.keys| == 0 {
    } else {
      WFPrefix(kvl, |kvl.keys| - 1);
      lenKeysLeWeightOver8(Kvl(DropLast(kvl.keys), DropLast(kvl.values)));
      kvlWeightEq(kvl);
      kvlWeightEq(Kvl(DropLast(kvl.keys), DropLast(kvl.values)));
    }
  }

  // This is far weaker than it could be, but it's probably good enough.
  // Weight is on the order of a few million, and I plan on using this lemma
  // to show that numbers fit within 64 bits.
  lemma lenKeysLeWeight(kvl: Kvl)
  requires WF(kvl)
  ensures |kvl.keys| <= WeightBucket(I(kvl))
  {
    lenKeysLeWeightOver8(kvl);
  }

  lemma WeightKvlInduct(kvl: Kvl, j: int)
  requires WF(kvl)
  requires 0 <= j < |kvl.keys|
  ensures WeightKvl(prefix(kvl, j as int)) +
      WeightKey(kvl.keys[j]) + WeightMessage(kvl.values[j])
          == WeightKvl(prefix(kvl, j as int + 1));

  method computeWeightKvl(kvl: Kvl)
  returns (weight: uint64)
  requires WF(kvl)
  requires WeightBucket(I(kvl)) < 0x1_0000_0000_0000_0000
  ensures weight as int == WeightBucket(I(kvl))
  {
    kvlWeightEq(kvl);
    lenKeysLeWeight(kvl);

    var j: uint64 := 0;
    var w: uint64 := 0;
    while j < |kvl.keys| as uint64
    invariant 0 <= j as int <= |kvl.keys|
    invariant w as int == WeightKvl(prefix(kvl, j as int))
    {
      WeightKvlInduct(kvl, j as int);
      kvlWeightPrefixLe(kvl, j as int + 1);

      w := w + WeightKeyUint64(kvl.keys[j]) + WeightMessageUint64(kvl.values[j]);
      j := j + 1;
    }
    weight := w;

    assert prefix(kvl, |kvl.keys|) == kvl;
  }

  function toKvl(bucket: Bucket) : (kvl: Kvl)
  requires WFBucket(bucket)
  ensures WF(kvl)
  ensures I(kvl) == bucket

  function toKvlSeq(buckets: BucketList) : (kvls: seq<Kvl>)
  requires forall i | 0 <= i < |buckets| :: WFBucket(buckets[i])
  ensures |kvls| == |buckets|
  ensures forall i | 0 <= i < |kvls| :: WF(kvls[i])
  ensures ISeq(kvls) == buckets

  function getMiddleKey(bucket: Bucket) : Key
  requires WFBucket(bucket)
  {
    var kvl := toKvl(bucket);
    if |kvl.keys| == 0 then
      [0] // Just pick an arbitary key
    else (
      var key := kvl.keys[|kvl.keys| / 2];
      if |key| == 0 then 
        [0]
      else
        key
    )
  }

  method GetMiddleKey(kvl: Kvl) returns (res: Key)
  requires WF(kvl)
  ensures WFBucket(I(kvl))
  ensures getMiddleKey(I(kvl)) == res
  {
    WFImpliesWFBucket(kvl); 
    assume kvl == toKvl(I(kvl));
    if |kvl.keys| == 0 {
      return [0];
    } else {
      var key := kvl.keys[|kvl.keys| / 2];
      if |key| == 0 {
        return [0];
      } else {
        return key;
      }
    }
  }

}
