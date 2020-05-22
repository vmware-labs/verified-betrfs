include "../Base/Message.i.dfy"
include "../Base/sequences.i.dfy"
include "../Base/Maps.s.dfy"
include "../Base/NativeArrays.s.dfy"
include "BucketsLib.i.dfy"
include "BucketWeights.i.dfy"
include "../Base/MallocAccounting.i.dfy"
//
// A list of key-message pairs, with unique, sorted keys.
// TODO(robj,thance): How is it used... in BucketImpl?
// NOTE(tjhance): this is mostly Impl-related stuff, but a bit of it is used by the Marshalling file
// TODO(tjhance): rename this to KMList because it's Keys and Messages, not Keys and Values
//
// VESTIGIAL -- do not bother trying to prove stuff here because this
// file is marked for deletion or major renovation.
//

module KVList {
  import opened ValueMessage`Internal
  import opened LBOI = Lexicographic_Byte_Order_Impl
  import opened Ord = LBOI.Ord
  import opened Sequences
  import opened Options
  import opened Maps
  import opened BucketsLib
  import opened BucketWeights
  import opened NativeTypes
  import NativeArrays
  import P = PivotsLib
  import SeqComparison
  import opened KeyType
  import MallocAccounting

  datatype Kvl = Kvl(keys: seq<Key>, messages: seq<Message>)

  predicate WF(kvl: Kvl) {
    && |kvl.keys| == |kvl.messages|
    && IsStrictlySorted(kvl.keys)
    && (forall i | 0 <= i < |kvl.messages| :: kvl.messages[i] != IdentityMessage())
  }

  // Reallocate the bytes of a kvl into contiguous memory.
  method AmassKvl(kvl: Kvl) returns (amassed: Kvl)
    requires WF(kvl)
    ensures WF(amassed)
    ensures I(kvl) == I(amassed)
  {
    assume false; // amass

    // Count how much space we'll need
    var i : uint64 := 0;
    var cumKeyLen:uint64 := 0;
    var cumMessageLen:uint64 := 0;
    while (i < |kvl.keys| as uint64)
    {
      cumKeyLen := cumKeyLen + |kvl.keys[i]| as uint64;
      cumMessageLen := cumMessageLen + |kvl.messages[i].value| as uint64;
      i := i + 1;
    }

    // String together the bytes
    var ary := new byte[cumKeyLen + cumMessageLen];
    var ptr:uint64 := 0;
    i := 0;
    while (i < |kvl.keys| as uint64)
    {
      NativeArrays.CopySeqIntoArray(kvl.keys[i], 0, ary, ptr, |kvl.keys[i]| as uint64);
      ptr := ptr + |kvl.keys[i]| as uint64;
      NativeArrays.CopySeqIntoArray<byte>(kvl.messages[i].value, 0, ary, ptr, |kvl.messages[i].value| as uint64);
      ptr := ptr + |kvl.messages[i].value| as uint64;
      i := i + 1;
    }

    // Glue into a seq
    MallocAccounting.set_amass_mode(true);
    var amassedSeq := ary[..];
    MallocAccounting.set_amass_mode(false);

    // String together the refs to the bytes, pointing into the amassed seq
    var keyAry := new Key[|kvl.keys| as uint64];
    var messageAry := new Message[|kvl.messages| as uint64];
    ptr := 0;
    i := 0;
    while (i < |kvl.keys| as uint64)
    {
      keyAry[i] := amassedSeq[ptr .. ptr+|kvl.keys[i]| as uint64];
      ptr := ptr + |kvl.keys[i]| as uint64;
      messageAry[i] := Message.Define(amassedSeq[ptr .. ptr+|kvl.messages[i].value| as uint64]);
      ptr := ptr + |kvl.messages[i].value| as uint64;
      i := i + 1;
    }

    // And finally glue the array of seq slice refs into seqs
    amassed := Kvl(keyAry[..], messageAry[..]);
  }

  function IMap(kvl: Kvl) : BucketMap
  requires |kvl.keys| == |kvl.messages|
  {
    BucketMapOfSeq(kvl.keys, kvl.messages)
  }

  function I(kvl: Kvl) : Bucket
  requires |kvl.keys| == |kvl.messages|
  {
    //B(IMap(kvl))
    BucketMapWithSeq(BucketMapOfSeq(kvl.keys, kvl.messages), kvl.keys, kvl.messages)
  }

  function {:opaque} ISeq(kvls: seq<Kvl>) : (s : seq<Bucket>)
  requires forall i | 0 <= i < |kvls| :: |kvls[i].keys| == |kvls[i].messages|
  ensures |s| == |kvls|
  ensures forall i | 0 <= i < |kvls| :: s[i] == I(kvls[i])
  {
    if |kvls| == 0 then [] else ISeq(DropLast(kvls)) + [I(Last(kvls))]
  }

  function prefix(kvl: Kvl, i: int) : Kvl
  requires 0 <= i <= |kvl.keys|
  requires 0 <= i <= |kvl.messages|
  {
    Kvl(kvl.keys[..i], kvl.messages[..i]) 
  }

  lemma WFPrefix(kvl: Kvl, i: int)
  requires WF(kvl)
  requires 0 <= i <= |kvl.keys|
  ensures WF(prefix(kvl, i))
  {
    reveal_IsStrictlySorted();
  }

  lemma IndexOfKey(kvl: Kvl, key: Key) returns (i : int)
  requires |kvl.keys| == |kvl.messages|
  requires key in IMap(kvl)
  ensures 0 <= i < |kvl.keys|
  ensures kvl.keys[i] == key
  decreases |kvl.keys|
  {
    reveal_BucketMapOfSeq();
    if key == Last(kvl.keys) {
      i := |kvl.keys| - 1;
    } else {
      i := IndexOfKey(Kvl(DropLast(kvl.keys), DropLast(kvl.messages)), key);
    }
  }

  lemma Imaps(kvl: Kvl, i: int)
  requires WF(kvl)
  requires 0 <= i < |kvl.keys|
  ensures MapsTo(IMap(kvl), kvl.keys[i], kvl.messages[i])
  decreases |kvl.keys|
  {
    reveal_BucketMapOfSeq();
    if (i == |kvl.keys| - 1) {
    } else {
      reveal_IsStrictlySorted();
      Imaps(Kvl(DropLast(kvl.keys), DropLast(kvl.messages)), i);
      assert kvl.keys[|kvl.keys| - 1] != kvl.keys[i];
    }
  }

  lemma WFImpliesWFBucket(kvl: Kvl)
  requires WF(kvl)
  ensures WFBucket(I(kvl))
  decreases |kvl.keys|
  {
    reveal_BucketMapOfSeq();
    if |kvl.keys| == 0 {
    } else {
      ghost var km' := prefix(kvl, |kvl.keys| - 1);
      WFPrefix(kvl, |kvl.keys| - 1);
      WFImpliesWFBucket(km');
    }
  }

  /////////////////////////
  //// Flush
  /////////////////////////

  function append(kvl: Kvl, key: Key, value: Message) : Kvl
  {
    Kvl(kvl.keys + [key], kvl.messages + [value])
  }

  lemma Iappend(kvl: Kvl, key: Key, value: Message)
  requires |kvl.keys| == |kvl.messages|
  ensures IMap(append(kvl, key, value)) == IMap(kvl)[key := value]
  {
    reveal_BucketMapOfSeq();
  }

  lemma Iprefix_append(kvl: Kvl, i: int)
  requires |kvl.keys| == |kvl.messages|
  requires 0 <= i < |kvl.keys|
  ensures IMap(prefix(kvl, i + 1)) == IMap(prefix(kvl, i))[kvl.keys[i] := kvl.messages[i]]
  {
    assert prefix(kvl, i + 1) == append(prefix(kvl, i), kvl.keys[i], kvl.messages[i]);
    Iappend(prefix(kvl, i), kvl.keys[i], kvl.messages[i]);
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
          flushIterate(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], child.messages[childIdx]))
        )
      ) else (
        if childIdx == |child.keys| then (
          if childrenIdx == |children| - 1 then (
            flushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.messages[parentIdx]))
          ) else (
            if lt(parent.keys[parentIdx], pivots[childrenIdx]) then (
              flushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.messages[parentIdx]))
            ) else (
              flushIterate(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], Kvl([], []))
            )
          )
        ) else (
          if child.keys[childIdx] == parent.keys[parentIdx] then (
            var m := Merge(parent.messages[parentIdx], child.messages[childIdx]);
            if m == IdentityMessage() then (
              flushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, cur)
            ) else (
              flushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], m))
            )
          ) else if lt(child.keys[childIdx], parent.keys[parentIdx]) then (
            flushIterate(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], child.messages[childIdx]))
          ) else (
            flushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.messages[parentIdx]))
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
    && WFBucketListProper(ISeq(children), pivots)
    && |pivots| + 1 == |children|
    && 0 <= parentIdx <= |parent.keys|
    && 0 <= childrenIdx <= |children|
    && (childrenIdx < |children| ==> 0 <= childIdx <= |children[childrenIdx].keys|)
    && |acc| == childrenIdx
    && (forall i | 0 <= i < childrenIdx :: WF(acc[i]))
    && ISeq(acc) == BucketListFlushPartial(I(parent), ISeq(children), pivots, childrenIdx)
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
    reveal_BucketMapOfSeq();
    if (|cur.keys| > 0) {
      var lastCurKey := cur.keys[|cur.keys| - 1];
      assert lastCurKey in IMap(cur);
      assert lastCurKey in (IMap(prefix(parent, parentIdx)).Keys + IMap(prefix(children[childrenIdx], childIdx)).Keys);
      if lastCurKey in IMap(prefix(parent, parentIdx)).Keys {
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
  ensures parentIdx < |parent.keys| ==> parent.keys[parentIdx] !in IMap(prefix(parent, parentIdx))
  ensures parentIdx < |parent.keys| ==> parent.keys[parentIdx] !in IMap(prefix(children[childrenIdx], childIdx))
  ensures childIdx < |children[childrenIdx].keys| ==> children[childrenIdx].keys[childIdx] !in IMap(prefix(parent, parentIdx))
  ensures childIdx < |children[childrenIdx].keys| ==> children[childrenIdx].keys[childIdx] !in IMap(prefix(children[childrenIdx], childIdx))
  {
    if parentIdx < |parent.keys| && parent.keys[parentIdx] in IMap(prefix(parent, parentIdx)) {
      var i := IndexOfKey(prefix(parent, parentIdx), parent.keys[parentIdx]);
      IsStrictlySortedImpliesLt(parent.keys, i, parentIdx);
    }
    if parentIdx < |parent.keys| && parent.keys[parentIdx] in IMap(prefix(children[childrenIdx], childIdx)) {
      var i := IndexOfKey(prefix(children[childrenIdx], childIdx), parent.keys[parentIdx]);
      IsStrictlySortedImpliesLte(children[childrenIdx].keys, i, childIdx - 1);
    }
    if childIdx < |children[childrenIdx].keys| && children[childrenIdx].keys[childIdx] in IMap(prefix(parent, parentIdx)) {
      var i := IndexOfKey(prefix(parent, parentIdx), children[childrenIdx].keys[childIdx]);
      IsStrictlySortedImpliesLte(parent.keys, i, parentIdx - 1);
    }
    if childIdx < |children[childrenIdx].keys| && children[childrenIdx].keys[childIdx] in IMap(prefix(children[childrenIdx], childIdx)) {
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
  ensures WF(append(cur, parent.keys[parentIdx], parent.messages[parentIdx]))
  ensures I(append(cur, parent.keys[parentIdx], parent.messages[parentIdx]))
      == BucketListItemFlush(I(prefix(parent, parentIdx + 1)), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx)
  {
    assume false;
    // flushIterateCurLastLt(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
    // flushIterateNextsNotInPrefixes(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
    // StrictlySortedAugment(cur.keys, parent.keys[parentIdx]);
    // BucketListItemFlushAddParentKey(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, parent.keys[parentIdx], parent.messages[parentIdx]);

    // P.RouteIs(pivots, parent.keys[parentIdx], childrenIdx);

    // Iappend(cur, parent.keys[parentIdx], parent.messages[parentIdx]);
    // Iprefix_append(parent, parentIdx);

    /*assert I(append(cur, parent.keys[parentIdx], parent.messages[parentIdx]))
        == I(cur)[parent.keys[parentIdx] := parent.messages[parentIdx]]
        == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx)[parent.keys[parentIdx] := parent.messages[parentIdx]]
        == BucketListItemFlush(I(prefix(parent, parentIdx))[parent.keys[parentIdx] := parent.messages[parentIdx]], I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx)
        == BucketListItemFlush(I(prefix(parent, parentIdx + 1)), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx);*/
  }

  lemma flushIterateAppendChild(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  requires 0 <= childrenIdx < |children|
  requires 0 <= childIdx < |children[childrenIdx].keys|
  ensures WF(append(cur, children[childrenIdx].keys[childIdx], children[childrenIdx].messages[childIdx]))
  ensures I(append(cur, children[childrenIdx].keys[childIdx], children[childrenIdx].messages[childIdx]))
      == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx + 1)), pivots, childrenIdx)
  {
    assume false;
    // var child := children[childrenIdx];
    // flushIterateCurLastLt(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
    // flushIterateNextsNotInPrefixes(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
    // StrictlySortedAugment(cur.keys, child.keys[childIdx]);
    // BucketListItemFlushAddChildKey(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, child.keys[childIdx], child.messages[childIdx]);

    // assert WFBucketAt(I(children[childrenIdx]), pivots, childrenIdx);
    // Imaps(child, childIdx);
    // assert child.keys[childIdx] in IMap(children[childrenIdx]);
    // assert P.Route(pivots, child.keys[childIdx]) == childrenIdx;

    // Iappend(cur, child.keys[childIdx], child.messages[childIdx]);
    // Iprefix_append(child, childIdx);

    /*assert I(append(cur, child.keys[childIdx], child.messages[childIdx]))
        == I(cur)[child.keys[childIdx] := child.messages[childIdx]]
        == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx)[child.keys[childIdx] := child.messages[childIdx]]
        == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx))[child.keys[childIdx] := child.messages[childIdx]], pivots, childrenIdx)
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
  requires Merge(parent.messages[parentIdx], children[childrenIdx].messages[childIdx]) != IdentityMessage()

  ensures WF(append(cur, parent.keys[parentIdx], Merge(parent.messages[parentIdx], children[childrenIdx].messages[childIdx])))
  ensures I(append(cur, parent.keys[parentIdx], Merge(parent.messages[parentIdx], children[childrenIdx].messages[childIdx])))
      == BucketListItemFlush(I(prefix(parent, parentIdx + 1)), I(prefix(children[childrenIdx], childIdx + 1)), pivots, childrenIdx)
  {
    assume false;
    // var child := children[childrenIdx];
    // flushIterateCurLastLt(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
    // flushIterateNextsNotInPrefixes(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
    // StrictlySortedAugment(cur.keys, child.keys[childIdx]);
    // BucketListItemFlushAddParentAndChildKey(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, child.keys[childIdx], parent.messages[parentIdx], child.messages[childIdx]);

    // assert WFBucketAt(I(children[childrenIdx]), pivots, childrenIdx);
    // Imaps(child, childIdx);
    // assert child.keys[childIdx] in IMap(children[childrenIdx]);
    // assert P.Route(pivots, child.keys[childIdx]) == childrenIdx;

    // Iappend(cur, parent.keys[parentIdx], Merge(parent.messages[parentIdx], children[childrenIdx].messages[childIdx]));
    // Iprefix_append(parent, parentIdx);
    // Iprefix_append(child, childIdx);

    /*assert I(append(cur, parent.keys[parentIdx], Merge(parent.messages[parentIdx], children[childrenIdx].messages[childIdx])))
        == I(cur)[parent.keys[parentIdx] := Merge(parent.messages[parentIdx], children[childrenIdx].messages[childIdx])]
        == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx)[parent.keys[parentIdx] := Merge(parent.messages[parentIdx], children[childrenIdx].messages[childIdx])]
        == BucketListItemFlush(I(prefix(parent, parentIdx))[parent.keys[parentIdx] := parent.messages[parentIdx]], I(prefix(children[childrenIdx], childIdx))[child.keys[childIdx] := child.messages[childIdx]], pivots, childrenIdx)
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
    ensures MapsAgreeOnKey(IMap(prefix(parent, parentIdx)), IMap(parent), key)
    {
      WFPrefix(parent, parentIdx);
      if (key in IMap(prefix(parent, parentIdx))) {
        var i := IndexOfKey(prefix(parent, parentIdx), key);
        Imaps(parent, i);
        Imaps(prefix(parent, parentIdx), i);
      } else if (key in IMap(parent)) {
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
         I(Kvl([],[])).b
      == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx + 1], 0)), pivots, childrenIdx + 1).b
  {
    reveal_BucketMapOfSeq();
    forall key | key in IMap(prefix(parent, parentIdx))
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
          flushIterateRes(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], child.messages[childIdx]));
        }
      } else {
        if childIdx == |child.keys| {
          if childrenIdx == |children| - 1 {
            flushIterateAppendParent(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
            flushIterateRes(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.messages[parentIdx]));
          } else {
            if lt(parent.keys[parentIdx], pivots[childrenIdx]) {
              flushIterateAppendParent(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
              flushIterateRes(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.messages[parentIdx]));
            } else {
              flushIterateCurEqBucketListItemFlush(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
              flushIterateIEmptyEqBucketListItemFlush(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
              flushIteratepivotLteChildKey0(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
              flushIterateRes(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], Kvl([], []));
            }
          }
        } else {
          if child.keys[childIdx] == parent.keys[parentIdx] {
            var m := Merge(parent.messages[parentIdx], child.messages[childIdx]);
            if m == IdentityMessage() {
              flushIterateRes(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, cur);
            } else {
              flushIterateAppendParentAndChild(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
              flushIterateRes(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], m));
            }
          } else if lt(child.keys[childIdx], parent.keys[parentIdx]) {
            flushIterateAppendChild(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
            flushIterateRes(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], child.messages[childIdx]));
          } else {
            flushIterateAppendParent(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
            flushIterateRes(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.messages[parentIdx]));
          }
        }
      }
    }
  }

  lemma flushRes(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>)
  requires WF(parent)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires WFBucketListProper(ISeq(children), pivots)
  ensures var f := flush(parent, children, pivots);
      && (forall i | 0 <= i < |f| :: WF(f[i]))
      && ISeq(f) == BucketListFlush(I(parent), ISeq(children), pivots)
  {
    reveal_BucketMapOfSeq();
    assert BucketListItemFlush(B(map[]), B(map[]), pivots, 0).b == map[];
    flushIterateRes(parent, children, pivots, 0, 0, 0, [], Kvl([], []));
  }

  method Flush(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>)
  returns (f : seq<Kvl>)
  requires WF(parent)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires WFBucketListProper(ISeq(children), pivots)
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
          cur_values[cur_idx] := child.messages[childIdx];
          assert append(Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), child.keys[childIdx], child.messages[childIdx]) == Kvl(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
          childIdx := childIdx + 1;
          cur_idx := cur_idx + 1;
        }
      } else {
        if childIdx == |child.keys| as uint64 {
          if childrenIdx == |children| as uint64 - 1 {
            cur_keys[cur_idx] := parent.keys[parentIdx];
            cur_values[cur_idx] := parent.messages[parentIdx];
            assert append(Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), parent.keys[parentIdx], parent.messages[parentIdx]) == Kvl(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
            parentIdx := parentIdx + 1;
            cur_idx := cur_idx + 1;
          } else {
            var c := cmp(parent.keys[parentIdx], pivots[childrenIdx]);
            if c < 0 {
              cur_keys[cur_idx] := parent.keys[parentIdx];
              cur_values[cur_idx] := parent.messages[parentIdx];
              assert append(Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), parent.keys[parentIdx], parent.messages[parentIdx]) == Kvl(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
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
            var m := Merge(parent.messages[parentIdx], child.messages[childIdx]);
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
            cur_values[cur_idx] := child.messages[childIdx];
            assert append(Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), child.keys[childIdx], child.messages[childIdx]) == Kvl(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
            childIdx := childIdx + 1;
            cur_idx := cur_idx + 1;
          } else {
            cur_keys[cur_idx] := parent.keys[parentIdx];
            cur_values[cur_idx] := parent.messages[parentIdx];
            assert append(Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), parent.keys[parentIdx], parent.messages[parentIdx]) == Kvl(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
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
  ensures m.None? ==> key !in I(kvl).b
  ensures m.Some? ==> key in I(kvl).b && I(kvl).b[key] == m.value
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
        m := Some(kvl.messages[mid]);
        Imaps(kvl, mid as int);
        return;
      } else if (c < 0) {
        hi := mid;
      } else {
        lo := mid + 1;
      }
    }

    if (key in IMap(kvl)) {
      ghost var j := IndexOfKey(kvl, key);
      if (lo > 0) { IsStrictlySortedImpliesLtIndices(kvl.keys, lo as int - 1, j as int); }
      if (hi as int < |kvl.keys|) { IsStrictlySortedImpliesLtIndices(kvl.keys, j as int, hi as int); }
    }

    m := None;
  }

  /////////////////////////
  //// Binary searching
  /////////////////////////

  method IndexOfFirstKeyGte(kvl: Kvl, key: Key)
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

  method IndexOfFirstKeyGt(kvl: Kvl, key: Key)
  returns (idx: uint64)
  requires WF(kvl)
  requires |kvl.keys| < 0x8000_0000_0000_0000
  ensures 0 <= idx as int <= |kvl.keys|
  ensures forall i | 0 <= i < idx as int :: lte(kvl.keys[i], key)
  ensures forall i | idx as int <= i as int < |kvl.keys| :: lt(key, kvl.keys[i])
  {
    var lo: uint64 := 0;
    var hi: uint64 := |kvl.keys| as uint64;

    while lo < hi
    invariant 0 <= lo as int <= |kvl.keys|
    invariant 0 <= hi as int <= |kvl.keys|
    invariant forall i | 0 <= i < lo as int :: lte(kvl.keys[i], key)
    invariant forall i | hi as int <= i < |kvl.keys| :: lt(key, kvl.keys[i])
    decreases hi as int - lo as int
    {
      reveal_IsStrictlySorted();

      var mid: uint64 := (lo + hi) / 2;
      var c := cmp(key, kvl.keys[mid]);
      if (c >= 0) {
        lo := mid + 1;
      } else {
        hi := mid;
      }
    }

    idx := lo;
  }

  /////////////////////////
  //// Splitting
  /////////////////////////

  method SplitLeft(kvl: Kvl, pivot: Key)
  returns (left: Kvl)
  requires WF(kvl)
  requires |kvl.keys| < 0x8000_0000_0000_0000
  ensures WF(left)
  ensures I(left) == SplitBucketLeft(I(kvl), pivot)
  {
    assume false;
    reveal_SplitBucketLeft();
    var idx := IndexOfFirstKeyGte(kvl, pivot);
    left := Kvl(kvl.keys[..idx], kvl.messages[..idx]);

    reveal_IsStrictlySorted();

    ghost var a := IMap(left);
    ghost var b := SplitBucketLeft(I(kvl), pivot).b;

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
    assume false;
    reveal_SplitBucketRight();
    var idx := IndexOfFirstKeyGte(kvl, pivot);
    right := Kvl(kvl.keys[idx..], kvl.messages[idx..]);

    reveal_IsStrictlySorted();

    ghost var a := IMap(right);
    ghost var b := SplitBucketRight(I(kvl), pivot).b;

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
      Kvl(j.keys + l.keys, j.messages + l.messages)
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
  requires WFBucketListProper(ISeq(kvls), pivots)
  ensures WF(join(kvls))
  ensures I(join(kvls)) == JoinBucketList(ISeq(kvls))
  {
    assume false;
  }

  method {:fuel JoinBucketList,0} {:fuel WFBucketList,0}
  Join(kvls: seq<Kvl>, ghost pivots: seq<Key>)
  returns (kvl: Kvl)
  requires forall i | 0 <= i < |kvls| :: WF(kvls[i])
  requires WFBucketListProper(ISeq(kvls), pivots)
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
    var messages := new Message[len];

    var j: uint64 := 0;
    var pos: uint64 := 0;
    while j < |kvls| as uint64
    invariant 0 <= j as int <= |kvls|
    invariant pos as int == LenSum(kvls, j as int)
    invariant 0 <= LenSum(kvls, j as int) <= keys.Length
    invariant keys[..LenSum(kvls, j as int)] == join(kvls[..j]).keys
    invariant messages[..LenSum(kvls, j as int)] == join(kvls[..j]).messages
    {
      LenSumPrefixLe(kvls, j as int + 1);

      assert LenSum(kvls, j as int + 1)
          == LenSum(kvls, j as int) + |kvls[j].keys|
          == pos as int + |kvls[j].keys|;

      assert pos as int + |kvls[j].keys| <= keys.Length;
      NativeArrays.CopySeqIntoArray(kvls[j].keys, 0, keys, pos, |kvls[j].keys| as uint64);
      NativeArrays.CopySeqIntoArray(kvls[j].messages, 0, messages, pos, |kvls[j].messages| as uint64);

      assert pos as int + |kvls[j].keys|
          == LenSum(kvls, j as int) + |kvls[j].keys|
          == LenSum(kvls, j as int + 1);

      assert DropLast(kvls[..j+1]) == kvls[..j];
      assert keys[..LenSum(kvls, j as int + 1)]
          == keys[..pos] + keys[pos .. LenSum(kvls, j as int + 1)]
          == join(kvls[..j]).keys + kvls[j].keys
          == join(kvls[..j+1]).keys;
      assert messages[..LenSum(kvls, j as int + 1)]
          == join(kvls[..j+1]).messages;

      pos := pos + |kvls[j].keys| as uint64;
      j := j + 1;
    }

    kvl := Kvl(keys[..], messages[..]);

    assert keys[..] == keys[..LenSum(kvls, j as int)];
    assert messages[..] == messages[..LenSum(kvls, j as int)];
    assert kvls[..j] == kvls;
    joinEqJoinBucketList(kvls, pivots);
  }*/

  /////////////////////////
  //// Splitting
  /////////////////////////

  /*function method EmptySeq(n: int) : (s : seq<Kvl>)
  requires n >= 0
  ensures |s| == n
  ensures forall i | 0 <= i < n :: WF(s[i])
  ensures forall i | 0 <= i < n :: s[i] == Kvl([],[])
  {
    if n == 0 then [] else EmptySeq(n-1) + [Kvl([],[])]
  }*/

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
    reveal_BucketMapOfSeq();
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
  requires |kvl.messages| < 0x1_0000_0000_0000_0000
  requires IsStrictlySorted(kvl.keys)
  requires forall i | 0 <= i < |kvl.messages| :: kvl.messages[i] != IdentityMessage()
  ensures b == WF(kvl)
  {
    if |kvl.keys| as uint64 != |kvl.messages| as uint64
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
  ensures I(kvl) == B(map[])
  {
    reveal_BucketMapOfSeq();
    Kvl([],[])
  }

  lemma Islice(kvls: seq<Kvl>, a: int, b: int)
  requires 0 <= a <= b <= |kvls|
  requires forall i | 0 <= i < |kvls| :: WF(kvls[i])
  ensures forall i | 0 <= i < |kvls[a..b]| :: WF(kvls[a..b][i])
  ensures ISeq(kvls[a..b]) == ISeq(kvls)[a..b]
  {
    reveal_BucketMapOfSeq();
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

  /////////////////////////
  //// Weight stuff
  /////////////////////////

  function WeightKvl(kvl: Kvl) : int
  {
    WeightKeyList(kvl.keys) + WeightMessageList(kvl.messages)
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
    // reveal_BucketMapOfSeq();
    // if |kvl.keys| == 0 {
    //   WeightBucketEmpty();
    // } else {
    //   WFPrefix(kvl, |kvl.keys| - 1);
    //   kvlWeightEq(Kvl(DropLast(kvl.keys), DropLast(kvl.messages)));
    //   if Last(kvl.keys) in IMap(Kvl(DropLast(kvl.keys), DropLast(kvl.messages))) {
    //     var i := IndexOfKey(Kvl(DropLast(kvl.keys), DropLast(kvl.messages)), Last(kvl.keys));
    //     reveal_IsStrictlySorted();
    //   }
    //   var prekvl := prefix(kvl, |kvl.keys| - 1);
    //   WFPrefix(kvl, |kvl.keys| - 1);
    //   WFImpliesWFBucket(prekvl);
    //   WeightBucketInduct(I(prekvl), Last(kvl.keys), Last(kvl.messages));
    //   calc {
    //     WeightKvl(kvl);
    //     WeightKvl(prekvl) + WeightKey(Last(kvl.keys)) + WeightMessage(Last(kvl.messages));
    //     WeightBucket(I(prekvl)) + WeightKey(Last(kvl.keys)) + WeightMessage(Last(kvl.messages));
    //   }
    // }
  }

  lemma kvlSeqWeightEq(kvls: seq<Kvl>)
  requires forall i | 0 <= i < |kvls| :: WF(kvls[i])
  ensures WeightKvlSeq(kvls) == WeightBucketList(ISeq(kvls))
  {
    reveal_WeightBucketList();
    if |kvls| == 0 {
    } else {
      kvlSeqWeightEq(DropLast(kvls));
      Islice(kvls, 0, |kvls| - 1);
      kvlWeightEq(Last(kvls));
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
      assume false;
      WFPrefix(kvl, |kvl.keys| - 1);
      kvlWeightPrefixLe(Kvl(DropLast(kvl.keys), DropLast(kvl.messages)), j);
      assert prefix(kvl, j) == prefix(Kvl(DropLast(kvl.keys), DropLast(kvl.messages)), j);
      assert WeightKvl(prefix(kvl, j))
          == WeightKvl(prefix(Kvl(DropLast(kvl.keys), DropLast(kvl.messages)), j))
          <= WeightKvl(Kvl(DropLast(kvl.keys), DropLast(kvl.messages)))
          <= WeightKvl(kvl);
    }
  }

  lemma lenKeysLeWeightOver4(kvl: Kvl)
  requires WF(kvl)
  ensures 4*|kvl.keys| <= WeightBucket(I(kvl))
  decreases |kvl.keys|
  {
    var bucket := I(kvl);
    KeyMultisetLeWeight(multiset(bucket.keys));
    SetCardinality(bucket.keys);
  }

  // This is far weaker than it could be, but it's probably good enough.
  // Weight is on the order of a few million, and I plan on using this lemma
  // to show that numbers fit within 64 bits.
  lemma lenKeysLeWeight(kvl: Kvl)
  requires WF(kvl)
  ensures |kvl.keys| <= WeightBucket(I(kvl))
  {
    lenKeysLeWeightOver4(kvl);
  }

  lemma WeightKvlInduct(kvl: Kvl, j: int)
  requires WF(kvl)
  requires 0 <= j < |kvl.keys|
  ensures WeightKvl(prefix(kvl, j as int)) +
      WeightKey(kvl.keys[j]) + WeightMessage(kvl.messages[j])
          == WeightKvl(prefix(kvl, j as int + 1));
  {
    assume false;
    assert DropLast(prefix(kvl, j as int + 1).messages)
        == prefix(kvl, j as int).messages;
    assert DropLast(prefix(kvl, j as int + 1).keys)
        == prefix(kvl, j as int).keys;
  }

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

      w := w + WeightKeyUint64(kvl.keys[j]) + WeightMessageUint64(kvl.messages[j]);
      j := j + 1;
    }
    weight := w;

    assert prefix(kvl, |kvl.keys|) == kvl;
  }

  function {:opaque} toKvl(bucket: Bucket) : (kvl: Kvl)
  requires WFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  ensures WF(kvl)
  ensures I(kvl) == bucket
  decreases bucket.b
  {
    reveal_BucketMapOfSeq();
    reveal_IsStrictlySorted();
    //reveal_WFBucket();
    assume false;

    if bucket.b.Keys == {} then (
      Kvl([], [])
    ) else (
      var key := maximum(bucket.b.Keys);
      var kvl1 := toKvl(B(MapRemove1(bucket.b, key)));
      StrictlySortedAugment(kvl1.keys, key);
      Kvl(kvl1.keys + [key], kvl1.messages + [bucket.b[key]])
    )
  }

  function {:opaque} toKvlSeq(buckets: BucketList) : (kvls: seq<Kvl>)
  requires BucketListWellMarshalled(buckets)
  requires forall i | 0 <= i < |buckets| :: WFBucket(buckets[i])
  ensures |kvls| == |buckets|
  ensures forall i | 0 <= i < |kvls| :: WF(kvls[i])
  ensures ISeq(kvls) == buckets
  {
    if |buckets| == 0 then (
      []
    ) else (
      toKvlSeq(DropLast(buckets)) + [toKvl(Last(buckets))]
    )
  }

  lemma lastIsMax(kvl: Kvl)
  requires WF(kvl)
  requires |kvl.keys| > 0
  ensures maximumKey(I(kvl).b.Keys) == Some(Last(kvl.keys))
  {
    Imaps(kvl, |kvl.keys| - 1);
    assert Last(kvl.keys) in IMap(kvl).Keys;
    forall key | key in IMap(kvl).Keys
    ensures lte(key, Last(kvl.keys))
    {
      var i := IndexOfKey(kvl, key);
      reveal_IsStrictlySorted();
    }
  }

  lemma lastIsNotInDropLast(kvl: Kvl)
  requires WF(kvl)
  requires |kvl.keys| > 0
  ensures WF(Kvl(DropLast(kvl.keys), DropLast(kvl.messages)))
  ensures Last(kvl.keys) !in IMap(Kvl(DropLast(kvl.keys), DropLast(kvl.messages)));
  {
    WFPrefix(kvl, |kvl.keys| - 1);
    if Last(kvl.keys) in IMap(Kvl(DropLast(kvl.keys), DropLast(kvl.messages))) {
      var i := IndexOfKey(Kvl(DropLast(kvl.keys), DropLast(kvl.messages)), Last(kvl.keys));
      assert kvl.keys[i] == Last(kvl.keys);
      reveal_IsStrictlySorted();
    }
  }

  lemma I_injective(kvl1: Kvl, kvl2: Kvl)
  requires WF(kvl1)
  requires WF(kvl2)
  requires IMap(kvl1) == IMap(kvl2)
  ensures kvl1 == kvl2
  decreases |kvl1.keys|
  {
    assume false;
    reveal_BucketMapOfSeq();
    reveal_IsStrictlySorted();
    if |kvl1.keys| == 0 {
    } else {
      lastIsMax(kvl1);
      lastIsMax(kvl2);
      assert Some(Last(kvl1.keys))
          == maximumKey(IMap(kvl1).Keys)
          == maximumKey(IMap(kvl2).Keys)
          == Some(Last(kvl2.keys));

      var key := Last(kvl1.keys);
      assert key == Last(kvl2.keys);
      lastIsNotInDropLast(kvl1);
      lastIsNotInDropLast(kvl2);
      //assert key !in IMap(Kvl(DropLast(kvl1.keys), DropLast(kvl1.messages)));
      //assert key !in IMap(Kvl(DropLast(kvl2.keys), DropLast(kvl2.messages)));
      assert IMap(Kvl(DropLast(kvl1.keys), DropLast(kvl1.messages)))
          == MapRemove1(IMap(kvl1), key)
          == MapRemove1(IMap(kvl2), key)
          == IMap(Kvl(DropLast(kvl2.keys), DropLast(kvl2.messages)));
      I_injective(
        prefix(kvl1, |kvl1.keys| - 1),
        prefix(kvl2, |kvl2.keys| - 1));
      assert Last(kvl1.messages) == Last(kvl2.messages);
    }
  }

  lemma toKvlI_eq(kvl: Kvl)
  requires WF(kvl)
  ensures WFBucket(I(kvl))
  ensures toKvl(I(kvl)) == kvl
  {
    WFImpliesWFBucket(kvl);
    assert I(toKvl(I(kvl))) == I(kvl);
    I_injective(toKvl(I(kvl)), kvl);
  }

}
