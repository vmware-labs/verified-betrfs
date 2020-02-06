include "KVList.i.dfy"
include "../../PivotBetree/Bounds.i.dfy"
include "PivotsLib.i.dfy"
include "BucketImpl.i.dfy"
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
  import opened BucketImpl
  import opened KeyType
  import NativeBenchmarking

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
          partialFlushIterate(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], child.messages[childIdx]), newParent, weightSlack)
        )
      ) else (
        if childIdx == |child.keys| then (
          if childrenIdx == |children| - 1 then (
            var w := WeightKey(parent.keys[parentIdx]) + WeightMessage(parent.messages[parentIdx]);
            if w <= weightSlack then (
              partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.messages[parentIdx]), newParent, weightSlack - w)
            ) else (
              partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, cur, append(newParent, parent.keys[parentIdx], parent.messages[parentIdx]), weightSlack)
            )
          ) else (
            if lt(parent.keys[parentIdx], pivots[childrenIdx]) then (
              var w := WeightKey(parent.keys[parentIdx]) + WeightMessage(parent.messages[parentIdx]);
              if w <= weightSlack then (
                partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.messages[parentIdx]), newParent, weightSlack - w)
              ) else (
                partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, cur, append(newParent, parent.keys[parentIdx], parent.messages[parentIdx]), weightSlack)
              )
            ) else (
              partialFlushIterate(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], Kvl([], []), newParent, weightSlack)
            )
          )
        ) else (
          if child.keys[childIdx] == parent.keys[parentIdx] then (
            var m := Merge(parent.messages[parentIdx], child.messages[childIdx]);
            if m == IdentityMessage() then (
              partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, cur, newParent, weightSlack + WeightKey(child.keys[childIdx]) + WeightMessage(child.messages[childIdx]))
            ) else (
              if weightSlack + WeightMessage(child.messages[childIdx]) >= WeightMessage(m) then (
                partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], m), newParent, weightSlack + WeightMessage(child.messages[childIdx]) - WeightMessage(m))
              ) else (
                partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], child.messages[childIdx]), append(newParent, parent.keys[parentIdx], parent.messages[parentIdx]), weightSlack)
              )
            )
          ) else if lt(child.keys[childIdx], parent.keys[parentIdx]) then (
            partialFlushIterate(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, append(cur, child.keys[childIdx], child.messages[childIdx]), newParent, weightSlack)
          ) else (
            var w := WeightKey(parent.keys[parentIdx]) + WeightMessage(parent.messages[parentIdx]);
            if w <= weightSlack then (
              partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, parent.keys[parentIdx], parent.messages[parentIdx]), newParent, weightSlack - w)
            ) else (
              partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, cur, append(newParent, parent.keys[parentIdx], parent.messages[parentIdx]), weightSlack)
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
    assume false;
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

  method PartialFlush(
    parentMutBucket: MutBucket,
    childrenMutBuckets: seq<MutBucket>,
    pivots: seq<Key>)
  returns (newParent: MutBucket, newChildren: seq<MutBucket>)
  /*requires WF(parent)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires |pivots| + 1 == |children|
  requires |children| <= MaxNumChildren()
  requires WeightBucket(I(parent)) <= MaxTotalBucketWeight()
  requires WeightBucketList(ISeq(children)) <= MaxTotalBucketWeight()
  requires childrenWeight as int == WeightKvlSeq(children)*/
  //ensures (newParent, newChildren) == partialFlush(parent, children, pivots)
  requires parentMutBucket.Inv()
  requires MutBucket.InvSeq(childrenMutBuckets)
  requires WFBucketList(MutBucket.ISeq(childrenMutBuckets), pivots)
  requires WeightBucket(parentMutBucket.I()) <= MaxTotalBucketWeight() as int
  requires WeightBucketList(MutBucket.ISeq(childrenMutBuckets)) <= MaxTotalBucketWeight() as int
  ensures newParent.Inv()
  ensures MutBucket.InvSeq(newChildren)
  ensures fresh(newParent.Repr)
  ensures fresh(MutBucket.ReprSeq(newChildren))
  ensures newParent.Repr !! MutBucket.ReprSeq(newChildren)
  ensures MutBucket.ReprSeqDisjoint(newChildren)
  ensures bucketPartialFlush(old(parentMutBucket.Bucket), old(MutBucket.ISeq(childrenMutBuckets)), pivots)
      == (newParent.Bucket, MutBucket.ISeq(newChildren))
  {
    NativeBenchmarking.start("partialFlush.init");
    assume false;
    reveal_partialFlush();

    var parent := parentMutBucket.GetKvl();
    var children := MutBucket.mutBucketSeqToKvlSeq(childrenMutBuckets);
    var childrenWeight := MutBucket.computeWeightOfSeq(childrenMutBuckets);

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
    var cur_messages := new Message[maxChildLen + |parent.keys| as uint64];
    var cur_idx: uint64 := 0;

    var newParent_keys := new Key[|parent.keys| as uint64];
    var newParent_messages := new Message[|parent.keys| as uint64];
    var newParent_idx: uint64 := 0;

    var initChildrenWeight := childrenWeight;
    kvlSeqWeightEq(children);
    var weightSlack: uint64 := MaxTotalBucketWeightUint64() - initChildrenWeight;
    var bucketStartWeightSlack: uint64 := weightSlack;

    NativeBenchmarking.end("partialFlush.init");
    NativeBenchmarking.start("partialFlush.main");

    while childrenIdx < |children| as uint64
    invariant 0 <= parentIdx as int <= |parent.keys|
    invariant 0 <= childrenIdx as int <= |children|
    invariant (childrenIdx as int < |children| ==> 0 <= childIdx as int <= |children[childrenIdx].keys|)
    invariant 0 <= cur_idx
    invariant 0 <= newParent_idx <= parentIdx
    invariant childrenIdx as int < |children| ==> cur_idx as int <= parentIdx as int + childIdx as int
    invariant childrenIdx as int == |children| ==> cur_idx == 0
    //invariant partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int)
        //== partialFlush(parent, children, pivots)
    decreases |children| - childrenIdx as int
    decreases |parent.keys| - parentIdx as int +
        (if childrenIdx as int < |children| then |children[childrenIdx].keys| - childIdx as int else 0)
    {
      ghost var ghosty := true;
      if ghosty {
        if parentIdx as int < |parent.messages| { WeightMessageBound(parent.messages[parentIdx]); }
        if childIdx as int < |children[childrenIdx].messages| { WeightMessageBound(children[childrenIdx].messages[childIdx]); }
      }

      var child := children[childrenIdx];
      if parentIdx == |parent.keys| as uint64 {
        if childIdx == |child.keys| as uint64 {
          var bucket := new MutBucket.InitWithWeight(
            Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]),
            childrenMutBuckets[childrenIdx].Weight + bucketStartWeightSlack - weightSlack);
          bucketStartWeightSlack := weightSlack;
          childrenIdx := childrenIdx + 1;
          childIdx := 0;
          acc := acc + [bucket];
          cur_idx := 0;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
        } else {
          cur_keys[cur_idx] := child.keys[childIdx];
          cur_messages[cur_idx] := child.messages[childIdx];
          assert append(Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), child.keys[childIdx], child.messages[childIdx]) == Kvl(cur_keys[..cur_idx+1], cur_messages[..cur_idx+1]);
          childIdx := childIdx + 1;
          cur_idx := cur_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
        }
      } else {
        if childIdx == |child.keys| as uint64 {
          if childrenIdx == |children| as uint64 - 1 {
            var w := WeightKeyUint64(parent.keys[parentIdx]) + WeightMessageUint64(parent.messages[parentIdx]);
            if w <= weightSlack {
              cur_keys[cur_idx] := parent.keys[parentIdx];
              cur_messages[cur_idx] := parent.messages[parentIdx];
              assert append(Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), parent.keys[parentIdx], parent.messages[parentIdx]) == Kvl(cur_keys[..cur_idx+1], cur_messages[..cur_idx+1]);
              weightSlack := weightSlack - w;
              parentIdx := parentIdx + 1;
              cur_idx := cur_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            } else {
              newParent_keys[newParent_idx] := parent.keys[parentIdx];
              newParent_messages[newParent_idx] := parent.messages[parentIdx];

              assert append(Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), parent.keys[parentIdx], parent.messages[parentIdx]) == Kvl(newParent_keys[..newParent_idx+1], newParent_messages[..newParent_idx+1]);

              parentIdx := parentIdx + 1;
              newParent_idx := newParent_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            }
          } else {
            var c := cmp(parent.keys[parentIdx], pivots[childrenIdx]);
            if c < 0 {
              var w := WeightKeyUint64(parent.keys[parentIdx]) + WeightMessageUint64(parent.messages[parentIdx]);
              if w <= weightSlack {
                cur_keys[cur_idx] := parent.keys[parentIdx];
                cur_messages[cur_idx] := parent.messages[parentIdx];
                assert append(Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), parent.keys[parentIdx], parent.messages[parentIdx]) == Kvl(cur_keys[..cur_idx+1], cur_messages[..cur_idx+1]);
                weightSlack := weightSlack - w;
                parentIdx := parentIdx + 1;
                cur_idx := cur_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
              } else {
                newParent_keys[newParent_idx] := parent.keys[parentIdx];
                newParent_messages[newParent_idx] := parent.messages[parentIdx];

                assert append(Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), parent.keys[parentIdx], parent.messages[parentIdx]) == Kvl(newParent_keys[..newParent_idx+1], newParent_messages[..newParent_idx+1]);

                parentIdx := parentIdx + 1;
                newParent_idx := newParent_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
              }
            } else {
              var bucket := new MutBucket.InitWithWeight(
                Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]),
                childrenMutBuckets[childrenIdx].Weight + bucketStartWeightSlack - weightSlack);
              bucketStartWeightSlack := weightSlack;

              acc := acc + [bucket];
              childrenIdx := childrenIdx + 1;
              childIdx := 0;
              cur_idx := 0;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            }
          }
        } else {
          var c := cmp(child.keys[childIdx], parent.keys[parentIdx]);
          if c == 0 {
            var m := Merge(parent.messages[parentIdx], child.messages[childIdx]);
            if m == IdentityMessage() {
              weightSlack := weightSlack + WeightKeyUint64(child.keys[childIdx]) + WeightMessageUint64(child.messages[childIdx]);
              parentIdx := parentIdx + 1;
              childIdx := childIdx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            } else {
              assume weightSlack <= 0x1_0000_0000;
              WeightMessageBound(m);

              if weightSlack + WeightMessageUint64(child.messages[childIdx]) >= WeightMessageUint64(m) {
                cur_keys[cur_idx] := parent.keys[parentIdx];
                cur_messages[cur_idx] := m;
                assert append(Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), parent.keys[parentIdx], m) == Kvl(cur_keys[..cur_idx+1], cur_messages[..cur_idx+1]);
                weightSlack := (weightSlack + WeightMessageUint64(child.messages[childIdx])) - WeightMessageUint64(m);
                cur_idx := cur_idx + 1;
                parentIdx := parentIdx + 1;
                childIdx := childIdx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
              } else {
                cur_keys[cur_idx] := parent.keys[parentIdx];
                cur_messages[cur_idx] := child.messages[childIdx];

                newParent_keys[newParent_idx] := parent.keys[parentIdx];
                newParent_messages[newParent_idx] := parent.messages[parentIdx];

                assert append(Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), parent.keys[parentIdx], child.messages[childIdx]) == Kvl(cur_keys[..cur_idx+1], cur_messages[..cur_idx+1]);
                assert append(Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), parent.keys[parentIdx], parent.messages[parentIdx]) == Kvl(newParent_keys[..newParent_idx+1], newParent_messages[..newParent_idx+1]);

                newParent_idx := newParent_idx + 1;
                cur_idx := cur_idx + 1;
                parentIdx := parentIdx + 1;
                childIdx := childIdx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
              }
            }
          } else if c < 0 {
            cur_keys[cur_idx] := child.keys[childIdx];
            cur_messages[cur_idx] := child.messages[childIdx];
            assert append(Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), child.keys[childIdx], child.messages[childIdx]) == Kvl(cur_keys[..cur_idx+1], cur_messages[..cur_idx+1]);
            childIdx := childIdx + 1;
            cur_idx := cur_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
          } else {
            var w := WeightKeyUint64(parent.keys[parentIdx]) + WeightMessageUint64(parent.messages[parentIdx]);
            if w <= weightSlack {
              cur_keys[cur_idx] := parent.keys[parentIdx];
              cur_messages[cur_idx] := parent.messages[parentIdx];
              assert append(Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), parent.keys[parentIdx], parent.messages[parentIdx]) == Kvl(cur_keys[..cur_idx+1], cur_messages[..cur_idx+1]);
              weightSlack := weightSlack - w;
              parentIdx := parentIdx + 1;
              cur_idx := cur_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            } else {
              newParent_keys[newParent_idx] := parent.keys[parentIdx];
              newParent_messages[newParent_idx] := parent.messages[parentIdx];

              assert append(Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), parent.keys[parentIdx], parent.messages[parentIdx]) == Kvl(newParent_keys[..newParent_idx+1], newParent_messages[..newParent_idx+1]);

              parentIdx := parentIdx + 1;
              newParent_idx := newParent_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            }
          }
        }
      }
    }

    NativeBenchmarking.end("partialFlush.main");
    NativeBenchmarking.start("partialFlush.end");

    newChildren := acc;
    newParent := new MutBucket(
      Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx])
    );

    NativeBenchmarking.end("partialFlush.end");
  }

  /*method MutBucketPartialFlush(parent: MutBucket, children: seq<MutBucket>, pivots: seq<Key>)
  returns (newParent: MutBucket, newChildren: seq<MutBucket>)
  requires parent.Inv()
  requires InvSeq(children)
  requires WFBucketList(ISeq(children), pivots)
  requires WeightBucket(parent.I()) <= MaxTotalBucketWeight() as int
  requires WeightBucketList(ISeq(children)) <= MaxTotalBucketWeight() as int
  ensures newParent.Inv()
  ensures InvSeq(newChildren)
  ensures fresh(newParent.Repr)
  ensures fresh(ReprSeq(newChildren))
  ensures newParent.Repr !! ReprSeq(newChildren)
  ensures ReprSeqDisjoint(newChildren)
  ensures KVListPartialFlush.bucketPartialFlush(parent.Bucket, ISeq(children), pivots)
      == (newParent.Bucket, ISeq(newChildren))
  {
    assume false;
    var kvlParent := parent.GetKvl();
    var kvlChildren := mutBucketSeqToKvlSeq(children);
    var childrenWeight := computeWeightOfSeq(children);
    newParent, newChildren := PartialFlush(kvlParent, kvlChildren, pivots, childrenWeight);
  }*/
}
