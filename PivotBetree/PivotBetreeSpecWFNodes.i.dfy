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
  ensures forall i | 0 <= i < |FlushOps(f)| :: InvNode(FlushOps(f)[i].node)
  ensures InvNode(FlushOps(f)[0].node)
  ensures InvNode(FlushOps(f)[1].node)
  {
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
  ensures InvNode(f.split_parent);
  ensures InvNode(f.left_child);
  ensures InvNode(f.right_child);
  ensures forall i | 0 <= i < |SplitOps(f)| :: InvNode(SplitOps(f)[i].node)
  {
    var split_parent := f.split_parent;
    var fused_parent := f.fused_parent;

    var lbound := (if f.slot_idx > 0 then Some(f.fused_parent.pivotTable[f.slot_idx - 1]) else None);
    var ubound := (if f.slot_idx < |f.fused_parent.pivotTable| then Some(f.fused_parent.pivotTable[f.slot_idx]) else None);
    var child := CutoffNode(f.fused_child, lbound, ubound);

    var left_child := f.left_child;
    var right_child := f.right_child;
    var slot_idx := f.slot_idx;
    var pivot := f.pivot;

    PivotNotMinimum(child.pivotTable, f.num_children_left - 1);
    WFPivotsInsert(fused_parent.pivotTable, slot_idx, pivot);

    WFSplitBucketInList(fused_parent.buckets, slot_idx, pivot, fused_parent.pivotTable);
    WeightSplitBucketInList(fused_parent.buckets, slot_idx, pivot);

    assert InvNode(split_parent);

    WFSlice(child.pivotTable, 0, f.num_children_left - 1);
    WFSuffix(child.pivotTable, f.num_children_left);

    BucketListHasWFBucketAtIdenticalSlice(child.buckets, child.pivotTable, left_child.buckets, left_child.pivotTable, 0, |left_child.buckets| - 1, 0);
    assert child.buckets[f.num_children_left..] == f.right_child.buckets;
    BucketListHasWFBucketAtIdenticalSlice(child.buckets, child.pivotTable, right_child.buckets, right_child.pivotTable, 0, |right_child.buckets| - 1, -f.num_children_left);

    WeightBucketListSlice(child.buckets, 0, f.num_children_left);
    WeightBucketListSuffix(child.buckets, f.num_children_left);

    assert InvNode(left_child);
    assert InvNode(right_child);
  }

  lemma ValidMergeWritesInvNodes(f: NodeFusion)
  requires ValidMerge(f)
  ensures InvNode(f.fused_parent);
  ensures InvNode(f.fused_child);
  ensures forall i | 0 <= i < |MergeOps(f)| :: InvNode(MergeOps(f)[i].node)
  {
    var split_parent := f.split_parent;
    var fused_parent := f.fused_parent;
    var fused_child := f.fused_child;
    var lbound := (if f.slot_idx > 0 then Some(f.split_parent.pivotTable[f.slot_idx - 1]) else None);
    var ubound := (if f.slot_idx + 1 < |f.split_parent.pivotTable| then Some(f.split_parent.pivotTable[f.slot_idx + 1]) else None);
    var left_child := CutoffNode(f.left_child, lbound, Some(f.pivot));
    var right_child := CutoffNode(f.right_child, Some(f.pivot), ubound);
    var slot_idx := f.slot_idx;
    var pivot := f.pivot;

    WeightBucketListConcat(left_child.buckets, right_child.buckets);

    WFPivotsRemoved(split_parent.pivotTable, slot_idx);
    
    reveal_MergeBucketsInList();

    BucketListHasWFBucketAtIdenticalSlice(split_parent.buckets, split_parent.pivotTable, fused_parent.buckets, fused_parent.pivotTable, 0, slot_idx - 1, 0);
    BucketListHasWFBucketAtIdenticalSlice(split_parent.buckets, split_parent.pivotTable, fused_parent.buckets, fused_parent.pivotTable, slot_idx + 1, |fused_parent.buckets| - 1, -1);

    WFMergeBucketsInList(split_parent.buckets, slot_idx, split_parent.pivotTable);
    WeightMergeBucketsInList(split_parent.buckets, slot_idx, split_parent.pivotTable);
    assert InvNode(fused_parent);
    PivotNotMinimum(split_parent.pivotTable, slot_idx);
    WFConcat3(left_child.pivotTable, pivot, right_child.pivotTable);

    BucketListHasWFBucketAtIdenticalSlice(left_child.buckets, left_child.pivotTable, fused_child.buckets, fused_child.pivotTable, 0, |left_child.buckets| - 1, 0);
    BucketListHasWFBucketAtIdenticalSlice(right_child.buckets, right_child.pivotTable, fused_child.buckets, fused_child.pivotTable, |left_child.buckets|, |fused_child.buckets| - 1, |left_child.buckets|);

    assert InvNode(fused_child);
  }

  lemma WFApplyRepivot(leaf: G.Node, pivots: seq<Key>)
  requires InvNode(leaf)
  requires leaf.children.None?
  requires WFPivots(pivots)
  requires |pivots| <= MaxNumChildren() - 1
  requires BucketListWellMarshalled(leaf.buckets)
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
  ensures forall i | 0 <= i < |RepivotOps(r)| :: InvNode(RepivotOps(r)[i].node)
  {
    WFApplyRepivot(r.leaf, r.pivots);
  }

  lemma ValidInsertWritesInvNodes(ins: MessageInsertion)
  requires ValidInsertion(ins)
  ensures forall i | 0 <= i < |InsertionOps(ins)| :: InvNode(InsertionOps(ins)[i].node)
  {
    var newroot := AddMessageToNode(ins.oldroot, ins.key, ins.msg);
    WeightBucketListInsert(ins.oldroot.buckets, ins.oldroot.pivotTable, ins.key, ins.msg);
    assert InvNode(newroot);
  }

  lemma ValidGrowWritesInvNodes(g: RootGrowth)
  requires ValidGrow(g)
  ensures forall i | 0 <= i < |GrowOps(g)| :: InvNode(GrowOps(g)[i].node)
  ensures InvNode(GrowOps(g)[0].node)
  ensures InvNode(GrowOps(g)[1].node)
  {
    var newroot := G.Node([], Some([g.newchildref]), [B(map[])]);
    WeightBucketListOneEmpty();
    assert InvNode(newroot);
  }

  // This lemma is useful for BetreeBlockCache
  lemma ValidStepWritesInvNodes(betreeStep: BetreeStep)
  requires ValidBetreeStep(betreeStep)
  ensures forall i | 0 <= i < |BetreeStepOps(betreeStep)| :: InvNode(BetreeStepOps(betreeStep)[i].node)
  {
    match betreeStep {
      case BetreeQuery(q) => {}
      case BetreeSuccQuery(q) => {}
      case BetreeInsert(ins) => {
        ValidInsertWritesInvNodes(ins);
      }
      case BetreeFlush(flush) => {
        ValidFlushWritesInvNodes(flush);
      }
      case BetreeGrow(growth) => {
        ValidGrowWritesInvNodes(growth);
      }
      case BetreeSplit(fusion) => {
        ValidSplitWritesInvNodes(fusion);
      }
      case BetreeMerge(fusion) => {
        ValidMergeWritesInvNodes(fusion);
      }
      case BetreeRepivot(r) => {
        ValidRepivotInvNodes(r);
      }
    }
  }
}
