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

  function partialFlushIterate(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl, newParent: Kvl, weightSlack: int) : (Kvl, seq<Kvl>)
  requires WF(parent)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires PSA.WF(cur.keys)
  requires PSA.WF(newParent.keys)
  requires |pivots| + 1 == |children|
  requires inputStringsTotal(parent, children) < 0x1_0000_0000 - 1
  requires inputLengthTotal(parent, children) < 0x1_0000_0000  
  requires 0 <= parentIdx <= PSA.psaNumStrings(parent.keys) as int
  requires 0 <= childrenIdx <= |children|
  requires childrenIdx < |children| ==> 0 <= childIdx <= PSA.psaNumStrings(children[childrenIdx].keys) as int
  requires PSA.psaNumStrings(cur.keys) as int <= inputStringsSoFar(parent, children, parentIdx, childrenIdx, childIdx)
  requires |cur.keys.data| <= inputLengthSoFar(parent, children, parentIdx, childrenIdx, childIdx)
  requires PSA.psaCanAppendSeq(newParent.keys, PSA.I(parent.keys)[parentIdx..])
  decreases |children| - childrenIdx
  decreases PSA.psaNumStrings(parent.keys) as int - parentIdx +
      (if childrenIdx < |children| then PSA.psaNumStrings(children[childrenIdx].keys) as int - childIdx else 0)
  {
    if childrenIdx == |children| then (
      (newParent, acc)
    ) else (
      var child := children[childrenIdx];

      if parentIdx == PSA.psaNumStrings(parent.keys) as int then (
        if childIdx == PSA.psaNumStrings(child.keys) as int then (
          partialFlushIterate(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], Kvl(PSA.EmptyPsa(), []), newParent, weightSlack)
        //) else if |cur.keys| == 0 then (
        //  partialFlushIterate(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [child], Kvl(PSA.EmptyPsa(), []))
        ) else (
          partialFlushIterate(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, append(cur, PSA.psaElement(child.keys, childIdx as uint64), child.messages[childIdx]), newParent, weightSlack)
        )
      ) else (
        if childIdx == PSA.psaNumStrings(child.keys) as int then (
          if childrenIdx == |children| - 1 then (
            var w := WeightKey(PSA.psaElement(parent.keys, parentIdx as uint64)) + WeightMessage(parent.messages[parentIdx]);
            if w <= weightSlack then (
              appendFromParent(parent, children, parentIdx, childrenIdx, childIdx, cur);
              partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]), newParent, weightSlack - w)
            ) else (
              assume false;
              partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, cur, append(newParent, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]), weightSlack)
            )
          ) else (
            if lt(PSA.psaElement(parent.keys, parentIdx as uint64), pivots[childrenIdx]) then (
              var w := WeightKey(PSA.psaElement(parent.keys, parentIdx as uint64)) + WeightMessage(parent.messages[parentIdx]);
              if w <= weightSlack then (
                appendFromParent(parent, children, parentIdx, childrenIdx, childIdx, cur);
                partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]), newParent, weightSlack - w)
              ) else (
                assume false;
                partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, cur, append(newParent, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]), weightSlack)
              )
            ) else (
              partialFlushIterate(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], Kvl(PSA.EmptyPsa(), []), newParent, weightSlack)
            )
          )
        ) else (
          if PSA.psaElement(child.keys, childIdx as uint64) == PSA.psaElement(parent.keys, parentIdx as uint64) then (
            var m := Merge(parent.messages[parentIdx], child.messages[childIdx]);
            if m == IdentityMessage() then (
              partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, cur, newParent, weightSlack + WeightKey(PSA.psaElement(child.keys, childIdx as uint64)) + WeightMessage(child.messages[childIdx]))
            ) else (
              if weightSlack + WeightMessage(child.messages[childIdx]) >= WeightMessage(m) then (
                appendFromParentChildMerge(parent, children, parentIdx, childrenIdx, childIdx, cur);                
                partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, append(cur, PSA.psaElement(child.keys, childIdx as uint64), m), newParent, weightSlack + WeightMessage(child.messages[childIdx]) - WeightMessage(m))
              ) else (
                assume false;
                partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, append(cur, PSA.psaElement(child.keys, childIdx as uint64), child.messages[childIdx]), append(newParent, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]), weightSlack)
              )
            )
          ) else if lt(PSA.psaElement(child.keys, childIdx as uint64), PSA.psaElement(parent.keys, parentIdx as uint64)) then (
            appendFromChild(parent, children, parentIdx, childrenIdx, childIdx, cur);
            partialFlushIterate(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, append(cur, PSA.psaElement(child.keys, childIdx as uint64), child.messages[childIdx]), newParent, weightSlack)
          ) else (
            var w := WeightKey(PSA.psaElement(parent.keys, parentIdx as uint64)) + WeightMessage(parent.messages[parentIdx]);
            if w <= weightSlack then (
              appendFromParent(parent, children, parentIdx, childrenIdx, childIdx, cur);
              partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]), newParent, weightSlack - w)
            ) else (
              assume false;
              partialFlushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, cur, append(newParent, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]), weightSlack)
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
    partialFlushIterate(parent, children, pivots, 0, 0, 0, [], Kvl(PSA.EmptyPsa(), []), Kvl(PSA.EmptyPsa(), []), MaxTotalBucketWeight() - WeightKvlSeq(children))
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
    assume false;
    reveal_partialFlush();

    var parent := parentMutBucket.GetKvl();
    var children := MutBucket.mutBucketSeqToKvlSeq(childrenMutBuckets);
    var childrenWeight := MutBucket.computeWeightOfSeq(childrenMutBuckets);

    WeightBucketLeBucketList(ISeq(children), 0);
    lenKeysLeWeight(children[0]);
    lenKeysLeWeight(parent);
    assert PSA.psaNumStrings(children[0].keys) as int + PSA.psaNumStrings(parent.keys) as int < 0x8000_0000_0000_0000;

    var maxChildLen: uint64 := 0;
    var idx: uint64 := 0;
    while idx < |children| as uint64
    invariant 0 <= idx as int <= |children|
    invariant forall i | 0 <= i < idx as int :: PSA.psaNumStrings(children[i].keys) <= maxChildLen
    invariant maxChildLen as int + PSA.psaNumStrings(parent.keys) as int < 0x8000_0000_0000_0000
    {
      WeightBucketLeBucketList(ISeq(children), idx as int);
      lenKeysLeWeight(children[idx]);
      if PSA.psaNumStrings(children[idx].keys) > maxChildLen {
        maxChildLen := PSA.psaNumStrings(children[idx].keys);
      }
      idx := idx + 1;
    }

    var parentIdx: uint64 := 0;
    var childrenIdx: uint64 := 0;
    var childIdx: uint64 := 0;
    var acc := [];

    var maxkeys := maxChildLen + PSA.psaNumStrings(parent.keys);
    var cur_keys := new PSA.DynamicPsa.PreSized(maxkeys as uint32, (maxkeys * MaxLen()) as uint32); //Key[maxChildLen + PSA.psaNumStrings(parent.keys) as uint64];
    var cur_messages := new Message[maxChildLen + PSA.psaNumStrings(parent.keys) as uint64];
    var cur_idx: uint64 := 0;

    var newParent_keys := new PSA.DynamicPsa.PreSized(PSA.psaNumStrings(parent.keys) as uint32, (PSA.psaNumStrings(parent.keys) * MaxLen()) as uint32); //Key[PSA.psaNumStrings(parent.keys) as uint64];
    var newParent_messages := new Message[PSA.psaNumStrings(parent.keys) as uint64];
    var newParent_idx: uint64 := 0;

    var initChildrenWeight := childrenWeight;
    kvlSeqWeightEq(children);
    var weightSlack: uint64 := MaxTotalBucketWeightUint64() - initChildrenWeight;
    var bucketStartWeightSlack: uint64 := weightSlack;

    while childrenIdx < |children| as uint64
    invariant 0 <= parentIdx <= PSA.psaNumStrings(parent.keys)
    invariant 0 <= childrenIdx as int <= |children|
    invariant (childrenIdx as int < |children| ==> 0 <= childIdx as int <= PSA.psaNumStrings(children[childrenIdx].keys) as int)
    invariant 0 <= cur_idx
    invariant 0 <= newParent_idx <= parentIdx
    invariant childrenIdx as int < |children| ==> cur_idx as int <= parentIdx as int + childIdx as int
    invariant childrenIdx as int == |children| ==> cur_idx == 0
    //invariant partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int)
        //== partialFlush(parent, children, pivots)
    decreases |children| - childrenIdx as int
    decreases PSA.psaNumStrings(parent.keys) - parentIdx +
        (if childrenIdx as int < |children| then PSA.psaNumStrings(children[childrenIdx].keys) - childIdx else 0)
    {
      ghost var ghosty := true;
      if ghosty {
        if parentIdx as int < |parent.messages| { WeightMessageBound(parent.messages[parentIdx]); }
        if childIdx as int < |children[childrenIdx].messages| { WeightMessageBound(children[childrenIdx].messages[childIdx]); }
      }

      var child := children[childrenIdx];
      if parentIdx == PSA.psaNumStrings(parent.keys) {
        if childIdx == PSA.psaNumStrings(child.keys) {
          var keys := cur_keys.toPsa();
          var bucket := new MutBucket.InitWithWeight(
            Kvl(keys, cur_messages[..cur_idx]),
            childrenMutBuckets[childrenIdx].Weight + bucketStartWeightSlack - weightSlack);
          bucketStartWeightSlack := weightSlack;
          childrenIdx := childrenIdx + 1;
          childIdx := 0;
          acc := acc + [bucket];
          cur_idx := 0;
          cur_keys.Prefix(0);
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
        } else {
          ghost var oldkeys := cur_keys.toPsa();
          cur_keys.Append(PSA.psaElement(child.keys, childIdx as uint64));
          cur_messages[cur_idx] := child.messages[childIdx];
          assert append(Kvl(oldkeys, cur_messages[..cur_idx]), PSA.psaElement(child.keys, childIdx as uint64), child.messages[childIdx]) == Kvl(cur_keys.toPsa(), cur_messages[..cur_idx+1]);
          childIdx := childIdx + 1;
          cur_idx := cur_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
        }
      } else {
        if childIdx == PSA.psaNumStrings(child.keys) {
          if childrenIdx == |children| as uint64 - 1 {
            var w := WeightKeyUint64(PSA.psaElement(parent.keys, parentIdx as uint64)) + WeightMessageUint64(parent.messages[parentIdx]);
            if w <= weightSlack {
              ghost var oldkeys := cur_keys.toPsa();
              cur_keys.Append(PSA.psaElement(parent.keys, parentIdx as uint64));
              cur_messages[cur_idx] := parent.messages[parentIdx];
              assert append(Kvl(oldkeys, cur_messages[..cur_idx]), PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]) == Kvl(cur_keys.toPsa(), cur_messages[..cur_idx+1]);
              weightSlack := weightSlack - w;
              parentIdx := parentIdx + 1;
              cur_idx := cur_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            } else {
              ghost var oldkeys := newParent_keys.toPsa();
              newParent_keys.Append(PSA.psaElement(parent.keys, parentIdx as uint64));
              newParent_messages[newParent_idx] := parent.messages[parentIdx];

              assert append(Kvl(oldkeys, newParent_messages[..newParent_idx]), PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]) == Kvl(newParent_keys.toPsa(), newParent_messages[..newParent_idx+1]);

              parentIdx := parentIdx + 1;
              newParent_idx := newParent_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            }
          } else {
            var c := cmp(PSA.psaElement(parent.keys, parentIdx as uint64), pivots[childrenIdx]);
            if c < 0 {
              var w := WeightKeyUint64(PSA.psaElement(parent.keys, parentIdx as uint64)) + WeightMessageUint64(parent.messages[parentIdx]);
              if w <= weightSlack {
                ghost var oldkeys := cur_keys.toPsa();
                cur_keys.Append(PSA.psaElement(parent.keys, parentIdx as uint64));
                cur_messages[cur_idx] := parent.messages[parentIdx];
                assert append(Kvl(oldkeys, cur_messages[..cur_idx]), PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]) == Kvl(cur_keys.toPsa(), cur_messages[..cur_idx+1]);
                weightSlack := weightSlack - w;
                parentIdx := parentIdx + 1;
                cur_idx := cur_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
              } else {
                ghost var oldkeys := newParent_keys.toPsa();
                newParent_keys.Append(PSA.psaElement(parent.keys, parentIdx as uint64));
                newParent_messages[newParent_idx] := parent.messages[parentIdx];

                assert append(Kvl(oldkeys, newParent_messages[..newParent_idx]), PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]) == Kvl(newParent_keys.toPsa(), newParent_messages[..newParent_idx+1]);

                parentIdx := parentIdx + 1;
                newParent_idx := newParent_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
              }
            } else {
              var bucket := new MutBucket.InitWithWeight(
                Kvl(cur_keys.toPsa(), cur_messages[..cur_idx]),
                childrenMutBuckets[childrenIdx].Weight + bucketStartWeightSlack - weightSlack);
              bucketStartWeightSlack := weightSlack;

              acc := acc + [bucket];
              childrenIdx := childrenIdx + 1;
              childIdx := 0;
              cur_idx := 0;
              cur_keys.Prefix(0);
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            }
          }
        } else {
          var c := cmp(PSA.psaElement(child.keys, childIdx as uint64), PSA.psaElement(parent.keys, parentIdx as uint64));
          if c == 0 {
            var m := Merge(parent.messages[parentIdx], child.messages[childIdx]);
            if m == IdentityMessage() {
              weightSlack := weightSlack + WeightKeyUint64(PSA.psaElement(child.keys, childIdx as uint64)) + WeightMessageUint64(child.messages[childIdx]);
              parentIdx := parentIdx + 1;
              childIdx := childIdx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            } else {
              assume weightSlack <= 0x1_0000_0000;
              WeightMessageBound(m);

              if weightSlack + WeightMessageUint64(child.messages[childIdx]) >= WeightMessageUint64(m) {
                ghost var oldkeys := cur_keys.toPsa();
                cur_keys.Append(PSA.psaElement(parent.keys, parentIdx as uint64));
                cur_messages[cur_idx] := m;
                assert append(Kvl(oldkeys, cur_messages[..cur_idx]), PSA.psaElement(parent.keys, parentIdx as uint64), m) == Kvl(cur_keys.toPsa(), cur_messages[..cur_idx+1]);
                weightSlack := (weightSlack + WeightMessageUint64(child.messages[childIdx])) - WeightMessageUint64(m);
                cur_idx := cur_idx + 1;
                parentIdx := parentIdx + 1;
                childIdx := childIdx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
              } else {
                ghost var oldkeys := cur_keys.toPsa();
                cur_keys.Append(PSA.psaElement(parent.keys, parentIdx as uint64));
                cur_messages[cur_idx] := child.messages[childIdx];

                ghost var oldparentkeys := newParent_keys.toPsa();
                newParent_keys.Append(PSA.psaElement(parent.keys, parentIdx as uint64));
                newParent_messages[newParent_idx] := parent.messages[parentIdx];

                assert append(Kvl(oldkeys, cur_messages[..cur_idx]), PSA.psaElement(parent.keys, parentIdx as uint64), child.messages[childIdx]) == Kvl(cur_keys.toPsa(), cur_messages[..cur_idx+1]);
                assert append(Kvl(oldparentkeys, newParent_messages[..newParent_idx]), PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]) == Kvl(newParent_keys.toPsa(), newParent_messages[..newParent_idx+1]);

                newParent_idx := newParent_idx + 1;
                cur_idx := cur_idx + 1;
                parentIdx := parentIdx + 1;
                childIdx := childIdx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
              }
            }
          } else if c < 0 {
            ghost var oldkeys := cur_keys.toPsa();
            cur_keys.Append(PSA.psaElement(child.keys, childIdx as uint64));
            cur_messages[cur_idx] := child.messages[childIdx];
            assert append(Kvl(oldkeys, cur_messages[..cur_idx]), PSA.psaElement(child.keys, childIdx as uint64), child.messages[childIdx]) == Kvl(cur_keys.toPsa(), cur_messages[..cur_idx+1]);
            childIdx := childIdx + 1;
            cur_idx := cur_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
          } else {
            var w := WeightKeyUint64(PSA.psaElement(parent.keys, parentIdx as uint64)) + WeightMessageUint64(parent.messages[parentIdx]);
            if w <= weightSlack {
              ghost var oldkeys := cur_keys.toPsa();
              cur_keys.Append(PSA.psaElement(parent.keys, parentIdx as uint64));
              cur_messages[cur_idx] := parent.messages[parentIdx];
              assert append(Kvl(oldkeys, cur_messages[..cur_idx]), PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]) == Kvl(cur_keys.toPsa(), cur_messages[..cur_idx+1]);
              weightSlack := weightSlack - w;
              parentIdx := parentIdx + 1;
              cur_idx := cur_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            } else {
              ghost var oldkeys := newParent_keys.toPsa();
              newParent_keys.Append(PSA.psaElement(parent.keys, parentIdx as uint64));
              newParent_messages[newParent_idx] := parent.messages[parentIdx];

              assert append(Kvl(oldkeys, newParent_messages[..newParent_idx]), PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]) == Kvl(newParent_keys.toPsa(), newParent_messages[..newParent_idx+1]);

              parentIdx := parentIdx + 1;
              newParent_idx := newParent_idx + 1;
//assert partialFlushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(cur_keys[..cur_idx], cur_messages[..cur_idx]), Kvl(newParent_keys[..newParent_idx], newParent_messages[..newParent_idx]), weightSlack as int) == partialFlush(parent, children, pivots);
            }
          }
        }
      }
    }

    newChildren := acc;
    newParent := new MutBucket(
      Kvl(newParent_keys.toPsa(), newParent_messages[..newParent_idx])
    );
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
