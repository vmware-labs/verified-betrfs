include "KVList.i.dfy"
include "../../PivotBetree/Bounds.i.dfy"
include "PivotsLib.i.dfy"
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
  import opened KeyType

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
