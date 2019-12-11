include "KVList.i.dfy"
include "../PivotBetree/Bounds.i.dfy"
include "../PivotBetree/PivotsLib.i.dfy"
//
// I guess sometimes we want to flush only part of a node's effective KVList,
// and KVList only specified full flushes?
// TODO(robj,thance): Improve this doc.
//

module KVListPartialFlush {
  import opened KVList
  import opened Lexicographic_Byte_Order
  import opened ValueMessage`Internal
  import opened BucketWeights
  import opened BucketsLib
  import opened NativeTypes
  import Pivots = PivotsLib
  import opened Bounds

  function partialFlushIterate(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl, newParent: Kvl, weightSlack: int) : (Kvl, seq<Kvl>)
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
      (newParent, acc)
    ) else (
      var child := children[childrenIdx];

      if parentIdx == |parent.keys| then (
        if childIdx == |child.keys| then (
          partialFlushIterate(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], Kvl([], []), newParent, weightSlack)
        //) else if |cur.keys| == 0 then (
        //  partialFlushIterate(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [child], Kvl([], []))
        ) else (
          partialFlushIterate(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], child.values[childIdx]), newParent, weightSlack)
        )
      ) else (
        if childIdx == |child.keys| then (
          if childrenIdx == |children| - 1 then (
            var w := WeightKey(parent.keys[parentIdx]) + WeightMessage(parent.values[parentIdx]);
            if w <= weightSlack then (
              partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.values[parentIdx]), newParent, weightSlack - w)
            ) else (
              partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, cur, append(newParent, parent.keys[parentIdx], parent.values[parentIdx]), weightSlack)
            )
          ) else (
            if lt(parent.keys[parentIdx], pivots[childrenIdx]) then (
              var w := WeightKey(parent.keys[parentIdx]) + WeightMessage(parent.values[parentIdx]);
              if w <= weightSlack then (
                partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.values[parentIdx]), newParent, weightSlack - w)
              ) else (
                partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, cur, append(newParent, parent.keys[parentIdx], parent.values[parentIdx]), weightSlack)
              )
            ) else (
              partialFlushIterate(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], Kvl([], []), newParent, weightSlack)
            )
          )
        ) else (
          if child.keys[childIdx] == parent.keys[parentIdx] then (
            var m := Merge(parent.values[parentIdx], child.values[childIdx]);
            if m == IdentityMessage() then (
              partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, cur, newParent, weightSlack + WeightKey(child.keys[childIdx]) + WeightMessage(child.values[childIdx]))
            ) else (
              if weightSlack + WeightMessage(child.values[childIdx]) >= WeightMessage(m) then (
                partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], m), newParent, weightSlack + WeightMessage(child.values[childIdx]) - WeightMessage(m))
              ) else (
                partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], child.values[childIdx]), append(newParent, parent.keys[parentIdx], parent.values[parentIdx]), weightSlack)
              )
            )
          ) else if lt(child.keys[childIdx], parent.keys[parentIdx]) then (
            partialFlushIterate(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], child.values[childIdx]), newParent, weightSlack)
          ) else (
            var w := WeightKey(parent.keys[parentIdx]) + WeightMessage(parent.values[parentIdx]);
            if w <= weightSlack then (
              partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.values[parentIdx]), newParent, weightSlack - w)
            ) else (
              partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, cur, append(newParent, parent.keys[parentIdx], parent.values[parentIdx]), weightSlack)
            )
          )
        )
      )
    )
  }

  function {:opaque} partialFlush(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>) : (Kvl, seq<Kvl>)
  requires WF(parent)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires |pivots| + 1 == |children|
  {
    partialFlushIterate(parent, children, pivots, 0, 0, 0, [], Kvl([], []), Kvl([], []), MaxTotalBucketWeight() - WeightKvlSeq(children))
  }

  lemma partialFlushWF(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>)
  requires WF(parent)
  requires Pivots.WFPivots(pivots)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires |pivots| + 1 == |children|
  requires WeightBucketList(ISeq(children)) <= MaxTotalBucketWeight()
  ensures var (newParent, newChildren) := partialFlush(parent, children, pivots);
      && WF(newParent)
      && (forall i | 0 <= i < |newChildren| :: WF(newChildren[i]))

  function bucketPartialFlush(parent: Bucket, children: seq<Bucket>, pivots: seq<Key>) : (res:(Bucket, seq<Bucket>))
  requires WFBucket(parent)
  requires Pivots.WFPivots(pivots)
  requires |pivots| + 1 == |children|
  requires WeightBucketList(children) <= MaxTotalBucketWeight()
  requires forall i | 0 <= i < |children| :: WFBucket(children[i])
  {
    partialFlushWF(toKvl(parent), toKvlSeq(children), pivots);

    var (newParent, newChildren) := partialFlush(toKvl(parent), toKvlSeq(children), pivots);
    (I(newParent), ISeq(newChildren))
  }

  lemma bucketPartialFlushRes(parent: Bucket, children: seq<Bucket>, pivots: seq<Key>)
  returns (flushedKeys: set<Key>)
  requires WFBucket(parent)
  requires Pivots.WFPivots(pivots)
  requires forall i | 0 <= i < |children| :: WFBucket(children[i])
  requires |pivots| + 1 == |children|
  requires WeightBucketList(children) <= MaxTotalBucketWeight()
  ensures var (newParent, newChildren) := bucketPartialFlush(parent, children, pivots);
      && WFBucket(newParent)
      && (forall i | 0 <= i < |newChildren| :: WFBucket(newChildren[i]))
      && newParent == BucketComplement(parent, flushedKeys)
      && newChildren == BucketListFlush(BucketIntersect(parent, flushedKeys), children, pivots)
      && WeightBucket(newParent) <= WeightBucket(parent)
      && WeightBucketList(newChildren) <= MaxTotalBucketWeight()

  method PartialFlush(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>, childrenWeight: uint64)
  returns (newParent: Kvl, newChildren: seq<Kvl>)
  requires WF(parent)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires |pivots| + 1 == |children|
  requires |children| <= MaxNumChildren()
  requires WeightBucket(I(parent)) <= MaxTotalBucketWeight()
  requires WeightBucketList(ISeq(children)) <= MaxTotalBucketWeight()
  requires childrenWeight as int == WeightKvlSeq(children)
  ensures (newParent, newChildren) == partialFlush(parent, children, pivots)
  {
    reveal_partialFlush();

    WeightBucketLeBucketList(ISeq(children), 0);
    lenKeysLeWeight(children[0]);
    lenKeysLeWeight(parent);
    assert |children[0].keys| + |parent.keys| < 0x8000_0000_0000_0000;

    var maxChildLen: uint64 := 0;
    var idx: uint64 := 0;
    while idx < |children| as uint64
    invariant 0 <= idx as int <= |children|
    invariant forall i | 0 <= i < idx as int :: |children[i].keys| <= maxChildLen as int
    invariant maxChildLen as int + |parent.keys| < 0x8000_0000_0000_0000
    {
      WeightBucketLeBucketList(ISeq(children), idx as int);
      lenKeysLeWeight(children[idx]);
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

    var newParent_keys := new Key[|parent.keys| as uint64];
    var newParent_values := new Message[|parent.keys| as uint64];
    var newParent_idx: uint64 := 0;

    var initChildrenWeight := childrenWeight;
    kvlSeqWeightEq(children);
    var weightSlack: uint64 := MaxTotalBucketWeightUint64() - initChildrenWeight;

    while childrenIdx < |children| as uint64
    invariant 0 <= parentIdx as int <= |parent.keys|
    invariant 0 <= childrenIdx as int <= |children|
    invariant (childrenIdx as int < |children| ==> 0 <= childIdx as int <= |children[childrenIdx].keys|)
    invariant 0 <= cur_idx
    invariant 0 <= newParent_idx <= parentIdx
    invariant childrenIdx as int < |children| ==> cur_idx as int <= parentIdx as int + childIdx as int
    invariant childrenIdx as int == |children| ==> cur_idx == 0
    invariant partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_values[..newParent_idx]), weightSlack as int)
        == partialFlush(parent, children, pivots)
    decreases |children| - childrenIdx as int
    decreases |parent.keys| - parentIdx as int +
        (if childrenIdx as int < |children| then |children[childrenIdx].keys| - childIdx as int else 0)
    {
      ghost var ghosty := true;
      if ghosty {
        if parentIdx as int < |parent.values| { WeightMessageBound(parent.values[parentIdx]); }
        if childIdx as int < |children[childrenIdx].values| { WeightMessageBound(children[childrenIdx].values[childIdx]); }
      }

      var child := children[childrenIdx];
      if parentIdx == |parent.keys| as uint64 {
        if childIdx == |child.keys| as uint64 {
          childrenIdx := childrenIdx + 1;
          childIdx := 0;
          acc := acc + [Kvl(cur_keys[..cur_idx], cur_values[..cur_idx])];
          cur_idx := 0;
assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_values[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
        } else {
          cur_keys[cur_idx] := child.keys[childIdx];
          cur_values[cur_idx] := child.values[childIdx];
          assert append(Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), child.keys[childIdx], child.values[childIdx]) == Kvl(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
          childIdx := childIdx + 1;
          cur_idx := cur_idx + 1;
assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_values[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
        }
      } else {
        if childIdx == |child.keys| as uint64 {
          if childrenIdx == |children| as uint64 - 1 {
            var w := WeightKeyUint64(parent.keys[parentIdx]) + WeightMessageUint64(parent.values[parentIdx]);
            if w <= weightSlack {
              cur_keys[cur_idx] := parent.keys[parentIdx];
              cur_values[cur_idx] := parent.values[parentIdx];
              assert append(Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), parent.keys[parentIdx], parent.values[parentIdx]) == Kvl(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
              weightSlack := weightSlack - w;
              parentIdx := parentIdx + 1;
              cur_idx := cur_idx + 1;
assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_values[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            } else {
              newParent_keys[newParent_idx] := parent.keys[parentIdx];
              newParent_values[newParent_idx] := parent.values[parentIdx];

              assert append(Kvl(newParent_keys[..newParent_idx], newParent_values[..newParent_idx]), parent.keys[parentIdx], parent.values[parentIdx]) == Kvl(newParent_keys[..newParent_idx+1], newParent_values[..newParent_idx+1]);

              parentIdx := parentIdx + 1;
              newParent_idx := newParent_idx + 1;
assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_values[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            }
          } else {
            var c := cmp(parent.keys[parentIdx], pivots[childrenIdx]);
            if c < 0 {
              var w := WeightKeyUint64(parent.keys[parentIdx]) + WeightMessageUint64(parent.values[parentIdx]);
              if w <= weightSlack {
                cur_keys[cur_idx] := parent.keys[parentIdx];
                cur_values[cur_idx] := parent.values[parentIdx];
                assert append(Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), parent.keys[parentIdx], parent.values[parentIdx]) == Kvl(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
                weightSlack := weightSlack - w;
                parentIdx := parentIdx + 1;
                cur_idx := cur_idx + 1;
assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_values[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
              } else {
                newParent_keys[newParent_idx] := parent.keys[parentIdx];
                newParent_values[newParent_idx] := parent.values[parentIdx];

                assert append(Kvl(newParent_keys[..newParent_idx], newParent_values[..newParent_idx]), parent.keys[parentIdx], parent.values[parentIdx]) == Kvl(newParent_keys[..newParent_idx+1], newParent_values[..newParent_idx+1]);

                parentIdx := parentIdx + 1;
                newParent_idx := newParent_idx + 1;
assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_values[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
              }
            } else {
              acc := acc + [Kvl(cur_keys[..cur_idx], cur_values[..cur_idx])];
              childrenIdx := childrenIdx + 1;
              childIdx := 0;
              cur_idx := 0;
assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_values[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            }
          }
        } else {
          var c := cmp(child.keys[childIdx], parent.keys[parentIdx]);
          if c == 0 {
            var m := Merge(parent.values[parentIdx], child.values[childIdx]);
            if m == IdentityMessage() {
              weightSlack := weightSlack + WeightKeyUint64(child.keys[childIdx]) + WeightMessageUint64(child.values[childIdx]);
              parentIdx := parentIdx + 1;
              childIdx := childIdx + 1;
assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_values[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            } else {
              assume weightSlack <= 0x1_0000_0000;
              WeightMessageBound(m);

              if weightSlack + WeightMessageUint64(child.values[childIdx]) >= WeightMessageUint64(m) {
                cur_keys[cur_idx] := parent.keys[parentIdx];
                cur_values[cur_idx] := m;
                assert append(Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), parent.keys[parentIdx], m) == Kvl(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
                weightSlack := (weightSlack + WeightMessageUint64(child.values[childIdx])) - WeightMessageUint64(m);
                cur_idx := cur_idx + 1;
                parentIdx := parentIdx + 1;
                childIdx := childIdx + 1;
assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_values[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
              } else {
                cur_keys[cur_idx] := parent.keys[parentIdx];
                cur_values[cur_idx] := child.values[childIdx];

                newParent_keys[newParent_idx] := parent.keys[parentIdx];
                newParent_values[newParent_idx] := parent.values[parentIdx];

                assert append(Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), parent.keys[parentIdx], child.values[childIdx]) == Kvl(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
                assert append(Kvl(newParent_keys[..newParent_idx], newParent_values[..newParent_idx]), parent.keys[parentIdx], parent.values[parentIdx]) == Kvl(newParent_keys[..newParent_idx+1], newParent_values[..newParent_idx+1]);

                newParent_idx := newParent_idx + 1;
                cur_idx := cur_idx + 1;
                parentIdx := parentIdx + 1;
                childIdx := childIdx + 1;
assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_values[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
              }
            }
          } else if c < 0 {
            cur_keys[cur_idx] := child.keys[childIdx];
            cur_values[cur_idx] := child.values[childIdx];
            assert append(Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), child.keys[childIdx], child.values[childIdx]) == Kvl(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
            childIdx := childIdx + 1;
            cur_idx := cur_idx + 1;
assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_values[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
          } else {
            var w := WeightKeyUint64(parent.keys[parentIdx]) + WeightMessageUint64(parent.values[parentIdx]);
            if w <= weightSlack {
              cur_keys[cur_idx] := parent.keys[parentIdx];
              cur_values[cur_idx] := parent.values[parentIdx];
              assert append(Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), parent.keys[parentIdx], parent.values[parentIdx]) == Kvl(cur_keys[..cur_idx+1], cur_values[..cur_idx+1]);
              weightSlack := weightSlack - w;
              parentIdx := parentIdx + 1;
              cur_idx := cur_idx + 1;
assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_values[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            } else {
              newParent_keys[newParent_idx] := parent.keys[parentIdx];
              newParent_values[newParent_idx] := parent.values[parentIdx];

              assert append(Kvl(newParent_keys[..newParent_idx], newParent_values[..newParent_idx]), parent.keys[parentIdx], parent.values[parentIdx]) == Kvl(newParent_keys[..newParent_idx+1], newParent_values[..newParent_idx+1]);

              parentIdx := parentIdx + 1;
              newParent_idx := newParent_idx + 1;
assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_values[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_values[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            }
          }
        }
      }
    }

    newChildren := acc;
    newParent := Kvl(newParent_keys[..newParent_idx], newParent_values[..newParent_idx]);
  }
}
