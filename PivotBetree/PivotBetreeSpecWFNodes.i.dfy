include "PivotBetreeSpec.i.dfy"

module PivotBetreeSpecWFNodes {
  import opened Options
  import opened PivotBetreeSpec`Internal
  import opened Maps
  import opened Sequences
  import opened BucketWeights
  import opened BucketsLib
  import opened Bounds
  import opened PivotsLib
  import opened ValueMessage
  import opened KeyType

  import MS = MapSpec
  import Keyspace = Lexicographic_Byte_Order

  lemma ValidFlushWritesInvNodes(f: NodeFlush)
  requires ValidFlush(f)
  requires forall i | 0 <= i < |FlushReads(f)| :: InvNode(FlushReads(f)[i].node)
  ensures forall i | 0 <= i < |FlushOps(f)| :: InvNode(FlushOps(f)[i].node)
  ensures InvNode(FlushOps(f)[0].node)
  ensures InvNode(FlushOps(f)[1].node)
  {
    assert InvNode(FlushReads(f)[0].node);
    assert InvNode(FlushReads(f)[1].node);

    var newparent := G.Node(
        f.parent.pivotTable,
        Some(f.parent.children.value[f.slotIndex := f.newchildref]),
        f.parent.buckets[f.slotIndex := BucketComplement(f.parent.buckets[f.slotIndex], f.keys)]
      );
    var newchild := AddMessagesToNode(f.child, BucketIntersect(f.parent.buckets[f.slotIndex], f.keys));

    WFBucketComplement(f.parent.buckets[f.slotIndex], f.keys);
    WFBucketIntersect(f.parent.buckets[f.slotIndex], f.keys);
    WeightBucketComplement(f.parent.buckets[f.slotIndex], f.keys);
    WeightBucketIntersect(f.parent.buckets[f.slotIndex], f.keys);
    WFBucketListFlush(BucketIntersect(f.parent.buckets[f.slotIndex], f.keys), f.child.buckets, f.child.pivotTable);
    WeightBucketListFlush(BucketIntersect(f.parent.buckets[f.slotIndex], f.keys), f.child.buckets, f.child.pivotTable);
    WeightBucketListShrinkEntry(f.parent.buckets, f.slotIndex, BucketComplement(f.parent.buckets[f.slotIndex], f.keys));

    /*forall i | 0 <= i < |newparent.buckets|
    ensures NodeHasWFBucketAt(newparent, i)
    {
      //if (i == f.slotIndex) {
      //  assert NodeHasWFBucketAt(newparent, i);
      //} else {
      assert NodeHasWFBucketAt(f.parent, i);
      //  assert NodeHasWFBucketAt(newparent, i);
      //}
    }*/

    reveal_BucketComplement();

    assert InvNode(newparent);
    assert InvNode(newchild);
  }

  lemma ValidSplitWritesInvNodes(f: NodeFusion)
  requires ValidSplit(f)
  requires forall i | 0 <= i < |SplitReads(f)| :: InvNode(SplitReads(f)[i].node)
  ensures InvNode(f.split_parent);
  ensures InvNode(f.left_child);
  ensures InvNode(f.right_child);
  ensures forall i | 0 <= i < |SplitOps(f)| :: InvNode(SplitOps(f)[i].node)
  {
    assert InvNode(SplitReads(f)[0].node);
    assert InvNode(SplitReads(f)[1].node);

    var split_parent := f.split_parent;
    var fused_parent := f.fused_parent;

    var lbound := (if f.slot_idx > 0 then Some(f.fused_parent.pivotTable[f.slot_idx - 1]) else None);
    var ubound := (if f.slot_idx < |f.fused_parent.pivotTable| then Some(f.fused_parent.pivotTable[f.slot_idx]) else None);
    var child := CutoffNode(f.fused_child, lbound, ubound);
    assume WFBucketListProper(child.buckets, child.pivotTable);

    var left_child := f.left_child;
    var right_child := f.right_child;
    var slot_idx := f.slot_idx;
    var pivot := f.pivot;

    PivotNotMinimum(child.pivotTable, f.num_children_left - 1);
    WFPivotsInsert(fused_parent.pivotTable, slot_idx, pivot);

    WFProperSplitBucketInList(fused_parent.buckets, slot_idx, pivot, fused_parent.pivotTable);
    WeightSplitBucketInListLe(fused_parent.buckets, slot_idx, pivot);

    assume BucketListWellMarshalled(split_parent.buckets);
    assert InvNode(split_parent);

    WFSlice(child.pivotTable, 0, f.num_children_left - 1);
    WFSuffix(child.pivotTable, f.num_children_left);

    BucketListHasWFBucketAtIdenticalSlice(child.buckets, child.pivotTable, left_child.buckets, left_child.pivotTable, 0, |left_child.buckets| - 1, 0);
    assert child.buckets[f.num_children_left..] == f.right_child.buckets;
    BucketListHasWFBucketAtIdenticalSlice(child.buckets, child.pivotTable, right_child.buckets, right_child.pivotTable, 0, |right_child.buckets| - 1, -f.num_children_left);

    WeightBucketListSlice(child.buckets, 0, f.num_children_left);
    WeightBucketListSuffix(child.buckets, f.num_children_left);

    assume BucketListWellMarshalled(left_child.buckets);
    assume BucketListWellMarshalled(right_child.buckets);
    assert InvNode(left_child);
    assert InvNode(right_child);
  }

  lemma ValidMergeWritesInvNodes(f: NodeFusion)
  requires ValidMerge(f)
  requires forall i | 0 <= i < |MergeReads(f)| :: InvNode(MergeReads(f)[i].node)
  ensures InvNode(f.fused_parent);
  ensures InvNode(f.fused_child);
  ensures forall i | 0 <= i < |MergeOps(f)| :: InvNode(MergeOps(f)[i].node)
  {
    assert InvNode(MergeReads(f)[0].node);
    assert InvNode(MergeReads(f)[1].node);
    assert InvNode(MergeReads(f)[2].node);

    var split_parent := f.split_parent;
    var fused_parent := f.fused_parent;
    var fused_child := f.fused_child;
    var lbound := (if f.slot_idx > 0 then Some(f.split_parent.pivotTable[f.slot_idx - 1]) else None);
    var ubound := (if f.slot_idx + 1 < |f.split_parent.pivotTable| then Some(f.split_parent.pivotTable[f.slot_idx + 1]) else None);
    var left_child := CutoffNode(f.left_child, lbound, Some(f.pivot));
    var right_child := CutoffNode(f.right_child, Some(f.pivot), ubound);
    var slot_idx := f.slot_idx;
    var pivot := f.pivot;

    assume WFBucketListProper(left_child.buckets, left_child.pivotTable);
    assume WFBucketListProper(right_child.buckets, right_child.pivotTable);

    WeightBucketListConcat(left_child.buckets, right_child.buckets);

    WFPivotsRemoved(split_parent.pivotTable, slot_idx);
    
    reveal_MergeBucketsInList();

    BucketListHasWFBucketAtIdenticalSlice(split_parent.buckets, split_parent.pivotTable, fused_parent.buckets, fused_parent.pivotTable, 0, slot_idx - 1, 0);
    BucketListHasWFBucketAtIdenticalSlice(split_parent.buckets, split_parent.pivotTable, fused_parent.buckets, fused_parent.pivotTable, slot_idx + 1, |fused_parent.buckets| - 1, -1);

    WFMergeBucketsInList(split_parent.buckets, slot_idx, split_parent.pivotTable);
    WeightMergeBucketsInListLe(split_parent.buckets, slot_idx, split_parent.pivotTable);
    assert InvNode(fused_parent);
    PivotNotMinimum(split_parent.pivotTable, slot_idx);
    WFConcat3(left_child.pivotTable, pivot, right_child.pivotTable);

    BucketListHasWFBucketAtIdenticalSlice(left_child.buckets, left_child.pivotTable, fused_child.buckets, fused_child.pivotTable, 0, |left_child.buckets| - 1, 0);
    BucketListHasWFBucketAtIdenticalSlice(right_child.buckets, right_child.pivotTable, fused_child.buckets, fused_child.pivotTable, |left_child.buckets|, |fused_child.buckets| - 1, |left_child.buckets|);

    assume BucketListWellMarshalled(fused_child.buckets);
    assert InvNode(fused_child);
  }

  lemma WFApplyRepivot(leaf: G.Node, pivots: seq<Key>)
  requires InvNode(leaf)
  requires leaf.children.None?
  requires WFPivots(pivots)
  requires |pivots| <= MaxNumChildren() - 1
  ensures InvNode(ApplyRepivot(leaf, pivots))
  {
    var j := JoinBucketList(leaf.buckets);
    var s := SplitBucketOnPivots(j, pivots);
    WFJoinBucketList(leaf.buckets);
    JoinBucketsSplitBucketOnPivotsCancel(j, pivots);
    WeightJoinBucketList(leaf.buckets);
    WeightSplitBucketOnPivots(j, pivots);
  }

  lemma ValidRepivotInvNodes(r: Repivot)
  requires ValidRepivot(r)
  requires forall i | 0 <= i < |RepivotReads(r)| :: InvNode(RepivotReads(r)[i].node)
  ensures forall i | 0 <= i < |RepivotOps(r)| :: InvNode(RepivotOps(r)[i].node)
  {
    assert InvNode(RepivotReads(r)[0].node);
    WFApplyRepivot(r.leaf, r.pivots);
  }

  lemma ValidInsertWritesInvNodes(ins: MessageInsertion)
  requires ValidInsertion(ins)
  requires forall i | 0 <= i < |InsertionReads(ins)| :: InvNode(InsertionReads(ins)[i].node)
  ensures forall i | 0 <= i < |InsertionOps(ins)| :: InvNode(InsertionOps(ins)[i].node)
  {
    assert InvNode(InsertionReads(ins)[0].node);
    var newroot := AddMessageToNode(ins.oldroot, ins.key, ins.msg);
    WeightBucketListInsert(ins.oldroot.buckets, ins.oldroot.pivotTable, ins.key, ins.msg);
    assert InvNode(newroot);
  }

  lemma ValidGrowWritesInvNodes(g: RootGrowth)
  requires ValidGrow(g)
  requires forall i | 0 <= i < |GrowReads(g)| :: InvNode(GrowReads(g)[i].node)
  ensures forall i | 0 <= i < |GrowOps(g)| :: InvNode(GrowOps(g)[i].node)
  ensures InvNode(GrowOps(g)[0].node)
  ensures InvNode(GrowOps(g)[1].node)
  {
    assert InvNode(GrowReads(g)[0].node);
    var newroot := G.Node([], Some([g.newchildref]), [B(map[])]);
    WeightBucketListOneEmpty();
    assert InvNode(newroot);
  }

  // This lemma is useful for BetreeBlockCache
  lemma ValidStepWritesInvNodes(betreeStep: BetreeStep)
  requires ValidBetreeStep(betreeStep)
  requires forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: InvNode(BetreeStepReads(betreeStep)[i].node)
  ensures forall i | 0 <= i < |BetreeStepOps(betreeStep)| :: InvNode(BetreeStepOps(betreeStep)[i].node)
  {
    match betreeStep {
      case BetreeQuery(q) => {}
      case BetreeSuccQuery(q) => {}
      case BetreeInsert(ins) => {
        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == InsertionReads(betreeStep.ins)[i].node;
        ValidInsertWritesInvNodes(ins);
      }
      case BetreeFlush(flush) => {
        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == FlushReads(betreeStep.flush)[i].node;
        ValidFlushWritesInvNodes(flush);
      }
      case BetreeGrow(growth) => {
        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == GrowReads(betreeStep.growth)[i].node;
        ValidGrowWritesInvNodes(growth);
      }
      case BetreeSplit(fusion) => {
        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == SplitReads(betreeStep.fusion)[i].node;
        ValidSplitWritesInvNodes(fusion);
      }
      case BetreeMerge(fusion) => {
        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == MergeReads(betreeStep.fusion)[i].node;
        ValidMergeWritesInvNodes(fusion);
      }
      case BetreeRepivot(r) => {
        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == RepivotReads(betreeStep.repivot)[i].node;
        ValidRepivotInvNodes(r);
      }
    }
  }
}
