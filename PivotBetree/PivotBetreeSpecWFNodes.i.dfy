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

  // TODO lots of proof duplication between WF and Inv lemmas
  // We could instead have the Inv lemmas call the WF lemmas

  lemma ValidFlushWritesWFNodes(f: NodeFlush)
  requires PivotBetreeSpec.ValidFlush(f)
  requires forall i | 0 <= i < |FlushReads(f)| :: WFNode(FlushReads(f)[i].node)
  ensures forall i | 0 <= i < |FlushOps(f)| :: WFNode(FlushOps(f)[i].node)
  ensures WFNode(FlushOps(f)[0].node)
  ensures WFNode(FlushOps(f)[1].node)
  {
    assert WFNode(FlushReads(f)[0].node);
    assert WFNode(FlushReads(f)[1].node);
    //WFBucketComplement(f.parent.buckets[f.slotIndex], f.keys);
    //WFBucketIntersect(f.parent.buckets[f.slotIndex], f.keys);
    //WeightBucketComplement(f.parent.buckets[f.slotIndex], f.keys);
    //WeightBucketIntersect(f.parent.buckets[f.slotIndex], f.keys);
    //WFBucketListFlush(BucketIntersect(f.parent.buckets[f.slotIndex], f.keys), f.child.buckets, f.child.pivotTable);
    //WeightBucketListFlush(BucketIntersect(f.parent.buckets[f.slotIndex], f.keys), f.child.buckets, f.child.pivotTable);
    WeightBucketListShrinkEntry(f.parent.buckets, f.slotIndex, f.newParentBucket);
    assert WFNode(FlushOps(f)[0].node);
    assert WFNode(FlushOps(f)[1].node);
  }

  lemma ValidFlushWritesInvNodes(f: NodeFlush)
  requires PivotBetreeSpec.ValidFlush(f)
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

  lemma WFBucketListProperCutoffNodeAndKeepLeft(
      node: G.Node,
      pivot: Key)
  requires InvNode(node)
  ensures
    var node' := CutoffNodeAndKeepLeft(node, pivot);
    WFBucketListProper(node'.buckets, node'.pivotTable)
  {
    reveal_CutoffNodeAndKeepLeft();
    var cLeft := CutoffForLeft(node.pivotTable, pivot);
    WFProperSplitBucketListLeft(node.buckets, node.pivotTable, cLeft, pivot);
  }

  lemma WFBucketListProperCutoffNodeAndKeepRight(
      node: G.Node,
      pivot: Key)
  requires WFNode(node)
  requires WFBucketListProper(node.buckets, node.pivotTable);
  ensures
    var node' := CutoffNodeAndKeepRight(node, pivot);
    WFBucketListProper(node'.buckets, node'.pivotTable)
  {
    reveal_CutoffNodeAndKeepRight();
    var cRight := CutoffForRight(node.pivotTable, pivot);
    WFProperSplitBucketListRight(node.buckets, node.pivotTable, cRight, pivot);
  }

  lemma WFBucketListProperCutoffNode(
      node: G.Node,
      lpivot: Option<Key>,
      rpivot: Option<Key>)
  requires InvNode(node)
  ensures
    var node' := CutoffNode(node, lpivot, rpivot);
    WFBucketListProper(node'.buckets, node'.pivotTable)
  {
    reveal_CutoffNode();
    var node' := CutoffNode(node, lpivot, rpivot);

    assert WFBucketListProper(node.buckets, node.pivotTable);

    match lpivot {
      case None => {
        match rpivot {
          case None => {
            assert WFBucketListProper(node'.buckets, node'.pivotTable);
          }
          case Some(rpivot) => {
            WFBucketListProperCutoffNodeAndKeepLeft(node, rpivot);
            assert WFBucketListProper(node'.buckets, node'.pivotTable);
          }
        }
      }
      case Some(lpivot) => {
        match rpivot {
          case None => {
            WFBucketListProperCutoffNodeAndKeepRight(node, lpivot);
            assert WFBucketListProper(node'.buckets, node'.pivotTable);
          }
          case Some(rpivot) => {
            var node1 := CutoffNodeAndKeepLeft(node, rpivot);
            var node' := CutoffNodeAndKeepRight(node1, lpivot);

            CutoffNodeCorrect(node, node1, node', lpivot, rpivot);
            WFBucketListProperCutoffNodeAndKeepLeft(node, rpivot);
            WFBucketListProperCutoffNodeAndKeepRight(node1, lpivot);

            assert WFBucketListProper(node'.buckets, node'.pivotTable);
          }
        }
      }
    }
  }

  lemma BucketListWellMarshalledCutoffNodeAndKeepLeft(
      node: G.Node,
      pivot: Key)
  requires WFNode(node)
  requires BucketListWellMarshalled(node.buckets)
  ensures
    var node' := CutoffNodeAndKeepLeft(node, pivot);
    BucketListWellMarshalled(node'.buckets)
  {
    reveal_CutoffNodeAndKeepLeft();
    var cLeft := CutoffForLeft(node.pivotTable, pivot);
  }

  lemma BucketListWellMarshalledCutoffNodeAndKeepRight(
      node: G.Node,
      pivot: Key)
  requires WFNode(node)
  requires BucketListWellMarshalled(node.buckets)
  ensures
    var node' := CutoffNodeAndKeepRight(node, pivot);
    BucketListWellMarshalled(node'.buckets)
  {
    reveal_CutoffNodeAndKeepRight();
    var cRight := CutoffForRight(node.pivotTable, pivot);
  }

  lemma BucketListWellMarshalledCutoffNode(
      node: G.Node,
      lpivot: Option<Key>,
      rpivot: Option<Key>)
  requires InvNode(node)
  ensures
    var node' := CutoffNode(node, lpivot, rpivot);
    BucketListWellMarshalled(node'.buckets)
  {
    reveal_CutoffNode();
    var node' := CutoffNode(node, lpivot, rpivot);

    assert BucketListWellMarshalled(node.buckets);

    match lpivot {
      case None => {
        match rpivot {
          case None => {
            assert BucketListWellMarshalled(node'.buckets);
          }
          case Some(rpivot) => {
            BucketListWellMarshalledCutoffNodeAndKeepLeft(node, rpivot);
            assert BucketListWellMarshalled(node'.buckets);
          }
        }
      }
      case Some(lpivot) => {
        match rpivot {
          case None => {
            BucketListWellMarshalledCutoffNodeAndKeepRight(node, lpivot);
            assert BucketListWellMarshalled(node'.buckets);
          }
          case Some(rpivot) => {
            var node1 := CutoffNodeAndKeepLeft(node, rpivot);
            var node' := CutoffNodeAndKeepRight(node1, lpivot);

            CutoffNodeCorrect(node, node1, node', lpivot, rpivot);
            BucketListWellMarshalledCutoffNodeAndKeepLeft(node, rpivot);
            BucketListWellMarshalledCutoffNodeAndKeepRight(node1, lpivot);

            assert BucketListWellMarshalled(node'.buckets);
          }
        }
      }
    }
  }

  lemma ValidSplitWritesWFNodes(f: NodeFusion)
  requires ValidSplit(f)
  requires forall i | 0 <= i < |SplitReads(f)| :: WFNode(SplitReads(f)[i].node)
  ensures WFNode(f.split_parent);
  ensures WFNode(f.left_child);
  ensures WFNode(f.right_child);
  ensures forall i | 0 <= i < |SplitOps(f)| :: WFNode(SplitOps(f)[i].node)
  {
    assert WFNode(SplitReads(f)[0].node);
    assert WFNode(SplitReads(f)[1].node);

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

    WeightSplitBucketInListLe(fused_parent.buckets, slot_idx, pivot);
    WFSplitBucketInList(fused_parent.buckets, slot_idx, pivot, fused_parent.pivotTable);

    WFSlice(child.pivotTable, 0, f.num_children_left - 1);
    WFSuffix(child.pivotTable, f.num_children_left);

    WeightBucketListSlice(child.buckets, 0, f.num_children_left);
    WeightBucketListSuffix(child.buckets, f.num_children_left);

    assert WFNode(f.split_parent);
    assert WFNode(f.left_child);
    assert WFNode(f.right_child);
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

    WFBucketListProperCutoffNode(f.fused_child, lbound, ubound);
    BucketListWellMarshalledCutoffNode(f.fused_child, lbound, ubound);

    var left_child := f.left_child;
    var right_child := f.right_child;
    var slot_idx := f.slot_idx;
    var pivot := f.pivot;

    PivotNotMinimum(child.pivotTable, f.num_children_left - 1);
    WFPivotsInsert(fused_parent.pivotTable, slot_idx, pivot);

    WFProperSplitBucketInList(fused_parent.buckets, slot_idx, pivot, fused_parent.pivotTable);
    WeightSplitBucketInListLe(fused_parent.buckets, slot_idx, pivot);

    assert BucketListWellMarshalled(split_parent.buckets) by {
      WellMarshalledSplitBucketInList(
          fused_parent.buckets, slot_idx, pivot);
    }
    assert InvNode(split_parent);

    WFSlice(child.pivotTable, 0, f.num_children_left - 1);
    WFSuffix(child.pivotTable, f.num_children_left);

    BucketListHasWFBucketAtIdenticalSlice(child.buckets, child.pivotTable, left_child.buckets, left_child.pivotTable, 0, |left_child.buckets| - 1, 0);
    assert child.buckets[f.num_children_left..] == f.right_child.buckets;
    BucketListHasWFBucketAtIdenticalSlice(child.buckets, child.pivotTable, right_child.buckets, right_child.pivotTable, 0, |right_child.buckets| - 1, -f.num_children_left);

    WeightBucketListSlice(child.buckets, 0, f.num_children_left);
    WeightBucketListSuffix(child.buckets, f.num_children_left);

    assert BucketListWellMarshalled(left_child.buckets) by {
      BucketListWellMarshalledSlice(child.buckets, 0, f.num_children_left);
    }
    assert BucketListWellMarshalled(right_child.buckets) by {
      BucketListWellMarshalledSlice(child.buckets, f.num_children_left, |child.buckets|);
    }
    assert InvNode(left_child);
    assert InvNode(right_child);
  }

  lemma ValidMergeWritesWFNodes(f: NodeFusion)
  requires ValidMerge(f)
  requires forall i | 0 <= i < |MergeReads(f)| :: WFNode(MergeReads(f)[i].node)
  ensures WFNode(f.fused_parent);
  ensures WFNode(f.fused_child);
  ensures forall i | 0 <= i < |MergeOps(f)| :: WFNode(MergeOps(f)[i].node)
  {
    assert WFNode(MergeReads(f)[0].node);
    assert WFNode(MergeReads(f)[1].node);
    assert WFNode(MergeReads(f)[2].node);

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

    WeightMergeBucketsInListLe(split_parent.buckets, slot_idx, split_parent.pivotTable);

    WFMergeBucketsInList(split_parent.buckets, slot_idx, split_parent.pivotTable);

    PivotNotMinimum(split_parent.pivotTable, slot_idx);
    WFConcat3(left_child.pivotTable, pivot, right_child.pivotTable);

    assert WFNode(f.fused_parent);
    assert WFNode(f.fused_child);
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

    var slot_idx := f.slot_idx;
    var pivot := f.pivot;

    var split_parent := f.split_parent;
    var fused_parent := f.fused_parent;
    var fused_child := f.fused_child;

    assert InvNode(fused_parent) by {
      WFPivotsRemoved(split_parent.pivotTable, slot_idx);
      
      assert forall i | 0 <= i <= slot_idx - 1 :: fused_parent.buckets[i] == split_parent.buckets[i]
        by { reveal_MergeBucketsInList(); }
      assert forall i | slot_idx + 1 <= i <= |fused_parent.buckets| - 1 :: fused_parent.buckets[i] == split_parent.buckets[i+1]
        by { reveal_MergeBucketsInList(); }

      BucketListHasWFBucketAtIdenticalSlice(split_parent.buckets, split_parent.pivotTable, fused_parent.buckets, fused_parent.pivotTable, 0, slot_idx - 1, 0);
      BucketListHasWFBucketAtIdenticalSlice(split_parent.buckets, split_parent.pivotTable, fused_parent.buckets, fused_parent.pivotTable, slot_idx + 1, |fused_parent.buckets| - 1, -1);

      WFProperMergeBucketsInList(split_parent.buckets, slot_idx, split_parent.pivotTable);
      WeightMergeBucketsInListLe(split_parent.buckets, slot_idx, split_parent.pivotTable);
    }

    assert InvNode(fused_child) by {
      var lbound := (if f.slot_idx > 0 then Some(f.split_parent.pivotTable[f.slot_idx - 1]) else None);
      var ubound := (if f.slot_idx + 1 < |f.split_parent.pivotTable| then Some(f.split_parent.pivotTable[f.slot_idx + 1]) else None);
      var left_child := CutoffNode(f.left_child, lbound, Some(f.pivot));
      var right_child := CutoffNode(f.right_child, Some(f.pivot), ubound);

      WFBucketListProperCutoffNode(f.left_child, lbound, Some(f.pivot));
      WFBucketListProperCutoffNode(f.right_child, Some(f.pivot), ubound);
      WeightBucketListConcat(left_child.buckets, right_child.buckets);

      PivotNotMinimum(split_parent.pivotTable, slot_idx);
      WFConcat3(left_child.pivotTable, pivot, right_child.pivotTable);

      assert WFPivots(fused_child.pivotTable); // This fixes a time-out somehow. -- robj
      BucketListHasWFBucketAtIdenticalSlice(left_child.buckets, left_child.pivotTable, fused_child.buckets, fused_child.pivotTable, 0, |left_child.buckets| - 1, 0);
      BucketListHasWFBucketAtIdenticalSlice(right_child.buckets, right_child.pivotTable, fused_child.buckets, fused_child.pivotTable, |left_child.buckets|, |fused_child.buckets| - 1, |left_child.buckets|);

      assert BucketListWellMarshalled(fused_child.buckets) by {
        BucketListWellMarshalledCutoffNode(f.left_child, lbound, Some(f.pivot));
        BucketListWellMarshalledCutoffNode(f.right_child, Some(f.pivot), ubound);
      }
    }
  }

  lemma WFApplyRepivot(leaf: G.Node, pivots: seq<Key>)
  requires WFNode(leaf)
  requires leaf.children.None?
  requires WFPivots(pivots)
  requires |pivots| <= MaxNumChildren() - 1
  ensures WFNode(ApplyRepivot(leaf, pivots))
  {
    var j := JoinBucketList(leaf.buckets);
    var s := SplitBucketOnPivots(j, pivots);
    WFJoinBucketList(leaf.buckets);
    JoinBucketsSplitBucketOnPivotsCancel(j, pivots);
    WeightJoinBucketList(leaf.buckets);
    WeightSplitBucketOnPivots(j, pivots);
  }

  lemma InvApplyRepivot(leaf: G.Node, pivots: seq<Key>)
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

  lemma ValidRepivotWFNodes(r: Repivot)
  requires ValidRepivot(r)
  requires forall i | 0 <= i < |RepivotReads(r)| :: WFNode(RepivotReads(r)[i].node)
  ensures forall i | 0 <= i < |RepivotOps(r)| :: WFNode(RepivotOps(r)[i].node)
  {
    assert WFNode(RepivotReads(r)[0].node);
    WFApplyRepivot(r.leaf, r.pivots);
  }

//~  lemma ValidRepivotInvNodes(r: Repivot)
//~  requires ValidRepivot(r)
//~  requires forall i | 0 <= i < |RepivotReads(r)| :: InvNode(RepivotReads(r)[i].node)
//~  ensures forall i | 0 <= i < |RepivotOps(r)| :: InvNode(RepivotOps(r)[i].node)
//~  {
//~    assert InvNode(RepivotReads(r)[0].node);
//~    InvApplyRepivot(r.leaf, r.pivots);
//~  }

  lemma ValidInsertWritesWFNodes(ins: MessageInsertion)
  requires ValidInsertion(ins)
  requires forall i | 0 <= i < |InsertionReads(ins)| :: WFNode(InsertionReads(ins)[i].node)
  ensures forall i | 0 <= i < |InsertionOps(ins)| :: WFNode(InsertionOps(ins)[i].node)
  {
    assert WFNode(InsertionReads(ins)[0].node);
    var newroot := AddMessageToNode(ins.oldroot, ins.key, ins.msg);
    WeightBucketListInsert(ins.oldroot.buckets, ins.oldroot.pivotTable, ins.key, ins.msg);
    assert WFNode(newroot);
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

  lemma ValidGrowWritesWFNodes(g: RootGrowth)
  requires ValidGrow(g)
  requires forall i | 0 <= i < |GrowReads(g)| :: WFNode(GrowReads(g)[i].node)
  ensures forall i | 0 <= i < |GrowOps(g)| :: WFNode(GrowOps(g)[i].node)
  ensures WFNode(GrowOps(g)[0].node)
  ensures WFNode(GrowOps(g)[1].node)
  {
    assert WFNode(GrowReads(g)[0].node);
    var newroot := G.Node([], Some([g.newchildref]), [B(map[])]);
    WeightBucketListOneEmpty();
    assert WFNode(newroot);
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

//~  lemma ValidStepWritesInvNodes(betreeStep: BetreeStep)
//~  requires ValidBetreeStep(betreeStep)
//~  requires forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: InvNode(BetreeStepReads(betreeStep)[i].node)
//~  ensures forall i | 0 <= i < |BetreeStepOps(betreeStep)| :: InvNode(BetreeStepOps(betreeStep)[i].node)
//~  {
//~    match betreeStep {
//~      case BetreeQuery(q) => {}
//~      case BetreeSuccQuery(q) => {}
//~      case BetreeInsert(ins) => {
//~        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == InsertionReads(betreeStep.ins)[i].node;
//~        ValidInsertWritesInvNodes(ins);
//~      }
//~      case BetreeFlush(flush) => {
//~        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == FlushReads(betreeStep.flush)[i].node;
//~        ValidFlushWritesInvNodes(flush);
//~      }
//~      case BetreeGrow(growth) => {
//~        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == GrowReads(betreeStep.growth)[i].node;
//~        ValidGrowWritesInvNodes(growth);
//~      }
//~      case BetreeSplit(fusion) => {
//~        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == SplitReads(betreeStep.fusion)[i].node;
//~        ValidSplitWritesInvNodes(fusion);
//~      }
//~      case BetreeMerge(fusion) => {
//~        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == MergeReads(betreeStep.fusion)[i].node;
//~        ValidMergeWritesInvNodes(fusion);
//~      }
//~      case BetreeRepivot(r) => {
//~        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == RepivotReads(betreeStep.repivot)[i].node;
//~        ValidRepivotInvNodes(r);
//~      }
//~    }
//~  }

  lemma ValidStepWritesWFNodes(betreeStep: BetreeStep)
  requires ValidBetreeStep(betreeStep)
  requires forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: WFNode(BetreeStepReads(betreeStep)[i].node)
  ensures forall i | 0 <= i < |BetreeStepOps(betreeStep)| :: WFNode(BetreeStepOps(betreeStep)[i].node)
  {
    match betreeStep {
      case BetreeQuery(q) => {}
      case BetreeSuccQuery(q) => {}
      case BetreeInsert(ins) => {
        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == InsertionReads(betreeStep.ins)[i].node;
        ValidInsertWritesWFNodes(ins);
      }
      case BetreeFlush(flush) => {
        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == FlushReads(betreeStep.flush)[i].node;
        ValidFlushWritesWFNodes(flush);
      }
      case BetreeGrow(growth) => {
        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == GrowReads(betreeStep.growth)[i].node;
        ValidGrowWritesWFNodes(growth);
      }
      case BetreeSplit(fusion) => {
        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == SplitReads(betreeStep.fusion)[i].node;
        ValidSplitWritesWFNodes(fusion);
      }
      case BetreeMerge(fusion) => {
        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == MergeReads(betreeStep.fusion)[i].node;
        ValidMergeWritesWFNodes(fusion);
      }
      case BetreeRepivot(r) => {
        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == RepivotReads(betreeStep.repivot)[i].node;
        ValidRepivotWFNodes(r);
      }
    }
  }
}
