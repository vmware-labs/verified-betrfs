include "Message.dfy"
include "../lib/sequences.dfy"
include "../lib/maps.dfy"
include "BucketsLib.dfy"

module KMTable {
  import opened ValueMessage`Internal
  import opened Lexicographic_Byte_Order
  import opened Sequences
  import opened Maps
  import opened BucketsLib
  import P = PivotsLib

  type Key = Element

  datatype KMTable = KMTable(keys: seq<Key>, values: seq<Message>)

  predicate WF(kmt: KMTable) {
    && |kmt.keys| == |kmt.values|
    && IsStrictlySorted(kmt.keys)
    && (forall i | 0 <= i < |kmt.values| :: kmt.values[i] != IdentityMessage())
  }

  function I(kmt: KMTable) : Bucket
  requires |kmt.keys| == |kmt.values|
  decreases |kmt.keys|
  {
    if |kmt.keys| == 0 then map[] else (
      I(KMTable(DropLast(kmt.keys), DropLast(kmt.values)))[Last(kmt.keys) := Last(kmt.values)]
    )
  }

  function ISeq(kmts: seq<KMTable>) : (s : seq<Bucket>)
  requires forall i | 0 <= i < |kmts| :: |kmts[i].keys| == |kmts[i].values|
  ensures |s| == |kmts|
  ensures forall i | 0 <= i < |kmts| :: s[i] == I(kmts[i])

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

  lemma IndexOfKey(kmt: KMTable, key: Key) returns (i : int)
  requires |kmt.keys| == |kmt.values|
  requires key in I(kmt)
  ensures 0 <= i < |kmt.keys|
  ensures kmt.keys[i] == key

  lemma Imaps(kmt: KMTable, i: int)
  requires WF(kmt)
  requires 0 <= i < |kmt.keys|
  ensures MapsTo(I(kmt), kmt.keys[i], kmt.values[i])

  //// Flush

  function append(kmt: KMTable, key: Key, value: Message) : KMTable
  {
    KMTable(kmt.keys + [key], kmt.values + [value])
  }

  function flush'(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>,
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
          flush'(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], KMTable([], []))
        ) else if childIdx == 0 then (
          flush'(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [child], KMTable([], []))
        ) else (
          flush'(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], child.values[childIdx]))
        )
      ) else (
        if childIdx == |child.keys| then (
          if childrenIdx == |children| - 1 then (
            flush'(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.values[parentIdx]))
          ) else (
            if lt(parent.keys[parentIdx], pivots[childrenIdx]) then (
              flush'(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.values[parentIdx]))
            ) else (
              flush'(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], KMTable([], []))
            )
          )
        ) else (
          if child.keys[childIdx] == parent.keys[parentIdx] then (
            var m := Merge(parent.values[parentIdx], child.values[childIdx]);
            if m == IdentityMessage() then (
              flush'(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, cur)
            ) else (
              flush'(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], m))
            )
          ) else if lt(child.keys[childIdx], parent.keys[parentIdx]) then (
            flush'(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], child.values[childIdx]))
          ) else (
            flush'(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.values[parentIdx]))
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
    flush'(parent, children, pivots, 0, 0, 0, [], KMTable([], []))
  }

  predicate flush'Inv(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>,
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

  lemma flush'CurLastLt(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<KMTable>, cur: KMTable)
  requires flush'Inv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  requires childrenIdx < |children|
  ensures |cur.keys| > 0 && parentIdx < |parent.keys| ==> lt(cur.keys[|cur.keys| - 1], parent.keys[parentIdx])
  ensures |cur.keys| > 0 && childIdx < |children[childrenIdx].keys| ==> lt(cur.keys[|cur.keys| - 1], children[childrenIdx].keys[childIdx])
  {
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

  lemma flush'NextsNotInPrefixes(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<KMTable>, cur: KMTable)
  requires flush'Inv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  requires childrenIdx < |children|
  ensures parentIdx < |parent.keys| ==> parent.keys[parentIdx] !in I(prefix(parent, parentIdx))
  ensures parentIdx < |parent.keys| ==> parent.keys[parentIdx] !in I(prefix(children[childrenIdx], childIdx))
  ensures childIdx < |children[childrenIdx].keys| ==> children[childrenIdx].keys[childIdx] !in I(prefix(parent, parentIdx))
  ensures childIdx < |children[childrenIdx].keys| ==> children[childrenIdx].keys[childIdx] !in I(prefix(children[childrenIdx], childIdx))

  lemma flush'AppendParent(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<KMTable>, cur: KMTable)
  requires flush'Inv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  requires 0 <= childrenIdx < |children|
  requires 0 <= parentIdx < |parent.keys|
  requires childrenIdx < |pivots| ==> lt(parent.keys[parentIdx], pivots[childrenIdx])
  ensures WF(append(cur, parent.keys[parentIdx], parent.values[parentIdx]))
  ensures I(append(cur, parent.keys[parentIdx], parent.values[parentIdx]))
      == BucketListItemFlush(I(prefix(parent, parentIdx + 1)), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx)
  {
    flush'CurLastLt(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
    flush'NextsNotInPrefixes(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
    StrictlySortedAugment(cur.keys, parent.keys[parentIdx]);
    BucketListItemFlushAddParentKey(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, parent.keys[parentIdx], parent.values[parentIdx]);

    P.RouteIs(pivots, parent.keys[parentIdx], childrenIdx);

    assert DropLast(parent.keys[.. parentIdx + 1]) == parent.keys[.. parentIdx];
    assert DropLast(parent.values[.. parentIdx + 1]) == parent.values[.. parentIdx];
    //assert I(prefix(parent, parentIdx + 1))
    //    == I(prefix(parent, parentIdx))[parent.keys[parentIdx] := parent.values[parentIdx]];

    /*assert I(append(cur, parent.keys[parentIdx], parent.values[parentIdx]))
        == I(cur)[parent.keys[parentIdx] := parent.values[parentIdx]]
        == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx)[parent.keys[parentIdx] := parent.values[parentIdx]]
        == BucketListItemFlush(I(prefix(parent, parentIdx))[parent.keys[parentIdx] := parent.values[parentIdx]], I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx)
        == BucketListItemFlush(I(prefix(parent, parentIdx + 1)), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx);*/
  }

  lemma flush'CurEqBucketListItemFlush(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<KMTable>, cur: KMTable)
  requires flush'Inv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
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

  lemma flush'Res(parent: KMTable, children: seq<KMTable>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<KMTable>, cur: KMTable)
  requires flush'Inv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  ensures var f := flush'(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
      && (forall i | 0 <= i < |f| :: |f[i].keys| == |f[i].values|)
      && ISeq(f) == BucketListFlush(I(parent), ISeq(children), pivots)
  decreases |children| - childrenIdx
  decreases |parent.keys| - parentIdx +
      (if childrenIdx < |children| then |children[childrenIdx].keys| - childIdx else 0)
  {
    reveal_IsStrictlySorted();

    if childrenIdx == |children| {
    } else {
      var child := children[childrenIdx];

      if parentIdx == |parent.keys| {
        if childIdx == |child.keys| {
          flush'CurEqBucketListItemFlush(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
          flush'Res(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], KMTable([], []));
        } else if childIdx == 0 {
          flush'Res(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [child], KMTable([], []));
        } else {
          flush'Res(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], child.values[childIdx]));
        }
      } else {
        if childIdx == |child.keys| {
          if childrenIdx == |children| - 1 {
            flush'AppendParent(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
            flush'Res(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.values[parentIdx]));
          } else {
            if lt(parent.keys[parentIdx], pivots[childrenIdx]) {
              flush'AppendParent(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
              flush'Res(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.values[parentIdx]));
            } else {
              flush'Res(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], KMTable([], []));
            }
          }
        } else {
          if child.keys[childIdx] == parent.keys[parentIdx] {
            var m := Merge(parent.values[parentIdx], child.values[childIdx]);
            if m == IdentityMessage() {
              flush'AppendParent(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
              flush'Res(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, cur);
            } else {
              flush'Res(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], m));
            }
          } else if lt(child.keys[childIdx], parent.keys[parentIdx]) {
            flush'Res(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], child.values[childIdx]));
          } else {
            flush'AppendParent(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
            flush'Res(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.values[parentIdx]));
          }
        }
      }
    }
   
  }
}
