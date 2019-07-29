include "BlockInterface.dfy"  
include "../lib/sequences.dfy"
include "../lib/Maps.dfy"
include "MapSpec.dfy"
include "Graph.dfy"
include "../lib/Option.dfy"
include "Message.dfy"
include "BetreeSpec.dfy"
include "Betree.dfy"
include "BetreeInv.dfy"
include "PivotBetreeSpec.dfy"
include "PivotsLib.dfy"

module PivotBetreeSpecRefinement {
  import B = BetreeSpec`Internal
  import P = PivotBetreeSpec`Internal
  import M = ValueMessage
  import MS = MapSpec
  import opened Maps
  import opened Sequences
  import opened Options
  import opened PivotsLib
  import PivotBetreeSpecWFNodes

  type Node = B.G.Node
  type PNode = P.G.Node

  type Value = B.G.Value
  type Reference = B.G.Reference
  type Buffer = B.G.Buffer

  function IChildren(node: PNode) : imap<Key, Reference>
  requires P.WFNode(node);
  {
    if node.children.Some? then (
      imap key :: node.children.value[Route(node.pivotTable, key)]
    ) else (
      imap[]
    )
  }

  function IBufferInternal(node: PNode) : Buffer
  requires P.WFNode(node);
  {
    imap key :: P.BucketLookup(node.buckets[Route(node.pivotTable, key)], key)
  }

  function IBufferLeaf(node: PNode) : Buffer
  requires P.WFNode(node);
  {
    imap key :: M.Merge(
      P.BucketLookup(node.buckets[Route(node.pivotTable, key)], key),
      M.DefineDefault()
    )
  }

  function IBuffer(node: PNode) : Buffer
  requires P.WFNode(node);
  {
    if node.children.Some? then
      IBufferInternal(node)
    else
      IBufferLeaf(node)
  }

  function INode(node: PNode) : Node
  requires P.WFNode(node);
  {
    B.G.Node(IChildren(node), IBuffer(node))
  }

  lemma WFNodeRefinesWFNode(node: PNode)
  requires P.WFNode(node)
  ensures B.WFNode(INode(node))
  {
  }

  function IReadOp(readOp: P.G.ReadOp) : B.G.ReadOp
  requires P.WFNode(readOp.node)
  {
    B.G.ReadOp(readOp.ref, INode(readOp.node))
  }

  function IReadOps(readOps: seq<P.G.ReadOp>) : seq<B.G.ReadOp>
  requires forall i | 0 <= i < |readOps| :: P.WFNode(readOps[i].node)
  ensures |readOps| == |IReadOps(readOps)|
  {
    if |readOps| == 0 then [] else
      IReadOps(readOps[..|readOps|-1]) + [IReadOp(readOps[|readOps|-1])]
  }

  function IQuery(q: P.LookupQuery) : B.LookupQuery
  requires P.ValidQuery(q)
  {
    B.LookupQuery(q.key, q.value, IReadOps(q.lookup))
  }

  function IInsertion(ins: P.MessageInsertion) : B.MessageInsertion
  requires P.ValidInsertion(ins)
  {
    B.MessageInsertion(ins.key, ins.msg, INode(ins.oldroot))
  }

  function KeysForSlot(node: PNode, slotIndex: int) : iset<Key>
  requires WFPivots(node.pivotTable)
  {
    iset key | Route(node.pivotTable, key) == slotIndex
  }

  function IFlush(flush: P.NodeFlush) : B.NodeFlush
  requires P.ValidFlush(flush)
  {
    B.NodeFlush(flush.parentref, INode(flush.parent), flush.childref, INode(flush.child), flush.newchildref, KeysForSlot(flush.parent, flush.slotIndex))
  }

  function IGrow(growth: P.RootGrowth) : B.RootGrowth
  requires P.ValidGrow(growth)
  {
    B.RootGrowth(INode(growth.oldroot), growth.newchildref)
  }

  function ISplit(split: P.NodeFusion) : B.Redirect
  requires P.ValidSplit(split)
  {
    PivotBetreeSpecWFNodes.ValidSplitWritesWFNodes(split);
    B.Redirect(
      split.parentref,
      INode(split.fused_parent),
      [split.fused_childref],
      imap[
        split.fused_childref := INode(split.fused_child)
      ],
      INode(split.split_parent),
      [split.left_childref, split.right_childref],
      imap[
        split.left_childref := INode(split.left_child),
        split.right_childref := INode(split.right_child)
      ],
      PivotTableBucketKeySet(split.fused_parent.pivotTable, split.slot_idx)
    )
  }

  function IMerge(split: P.NodeFusion) : B.Redirect
  requires P.ValidMerge(split)
  {
    PivotBetreeSpecWFNodes.ValidMergeWritesWFNodes(split);
    B.Redirect(
      split.parentref,
      INode(split.split_parent),
      [split.left_childref, split.right_childref],
      imap[
        split.left_childref := INode(split.left_child),
        split.right_childref := INode(split.right_child)
      ],
      INode(split.fused_parent),
      [split.fused_childref],
      imap[
        split.fused_childref := INode(split.fused_child)
      ],
      PivotTableBucketKeySet(split.fused_parent.pivotTable, split.slot_idx)
    )
  }

  function IStep(betreeStep: P.BetreeStep) : B.BetreeStep
  requires !betreeStep.BetreeRepivot?
  requires P.ValidBetreeStep(betreeStep)
  {
    match betreeStep {
      case BetreeQuery(q) => B.BetreeQuery(IQuery(q))
      case BetreeInsert(ins) => B.BetreeInsert(IInsertion(ins))
      case BetreeFlush(flush) => B.BetreeFlush(IFlush(flush))
      case BetreeGrow(growth) => B.BetreeGrow(IGrow(growth))
      case BetreeSplit(fusion) => B.BetreeRedirect(ISplit(fusion))
      case BetreeMerge(fusion) => B.BetreeRedirect(IMerge(fusion))
    }
  }

  lemma RefinesLookup(lookup: P.Lookup, key: Key)
  requires P.WFLookupForKey(lookup, key)
  ensures B.WFLookupForKey(IReadOps(lookup), key)
  {
    if (|lookup| == 1) {
    } else {
      forall idx | P.ValidLayerIndex(DropLast(lookup), idx) && idx < |DropLast(lookup)| - 1
      ensures P.LookupFollowsChildRefAtLayer(key, DropLast(lookup), idx)
      {
        assert P.LookupFollowsChildRefAtLayer(key, lookup, idx);
        //assert DropLast(lookup)[idx] == lookup[idx];
        //assert DropLast(lookup)[idx+1] == lookup[idx+1];
      }
      RefinesLookup(DropLast(lookup), key);
      forall idx | B.ValidLayerIndex(IReadOps(lookup), idx) && idx < |IReadOps(lookup)| - 1
      ensures key in IReadOps(lookup)[idx].node.children
      ensures B.LookupFollowsChildRefAtLayer(key, IReadOps(lookup), idx)
      {
        if idx < |lookup| - 2 {
          assert B.LookupFollowsChildRefAtLayer(key, IReadOps(DropLast(lookup)), idx);
          assert key in IReadOps(DropLast(lookup))[idx].node.children;
          //assert key in IReadOps(lookup)[idx].node.children;
          assert B.LookupFollowsChildRefAtLayer(key, IReadOps(lookup), idx);
        } else {
          assert P.LookupFollowsChildRefAtLayer(key, lookup, |lookup|-2);
          /*
          assert lookup[|lookup|-2].node.children.Some?;
          assert key in IChildren(lookup[|lookup|-2].node);
          assert key in INode(lookup[|lookup|-2].node).children;
          assert key in IReadOp(lookup[|lookup|-2]).node.children;
          assert key in IReadOps(lookup)[idx].node.children;
          assert B.LookupFollowsChildRefAtLayer(key, IReadOps(lookup), idx);
          */
        }
      }
    }
  }

  lemma RefinesInterpretLookup(lookup: P.Lookup, key: Key)
  requires P.WFLookupForKey(lookup, key)
  requires Last(lookup).node.children.Some?
  ensures B.WFLookupForKey(IReadOps(lookup), key)
  ensures B.InterpretLookup(IReadOps(lookup), key) == P.InterpretLookup(lookup, key)
  {
    RefinesLookup(lookup, key);

    if |lookup| == 1 {
      /*
      assert INode(lookup[0].node).buffer[key]
          == P.NodeLookup(lookup[0].node, key);
      assert B.InterpretLookup(IReadOps(lookup), key)
          == B.InterpretLookup([IReadOp(lookup[0])], key)
          == B.G.M.Merge(
            B.G.M.Update(B.G.M.NopDelta()),
            INode(lookup[0].node).buffer[key])
          == P.InterpretLookup(lookup, key);
      */
    } else {
      forall idx | P.ValidLayerIndex(DropLast(lookup), idx) && idx < |DropLast(lookup)| - 1
      ensures P.LookupFollowsChildRefAtLayer(key, DropLast(lookup), idx)
      {
        assert P.LookupFollowsChildRefAtLayer(key, lookup, idx);
      }

      assert P.LookupFollowsChildRefAtLayer(key, lookup, |lookup|-2);
      RefinesInterpretLookup(DropLast(lookup), key);
      assert B.InterpretLookup(IReadOps(lookup), key) == P.InterpretLookup(lookup, key);
    }
  }

  lemma RefinesInterpretLookupAccountingForLeaf(lookup: P.Lookup, key: Key, value: Value)
  requires P.WFLookupForKey(lookup, key)
  ensures B.WFLookupForKey(IReadOps(lookup), key)
  ensures B.InterpretLookup(IReadOps(lookup), key) == P.InterpretLookupAccountingForLeaf(lookup, key)
  {
    RefinesLookup(lookup, key);

    if (Last(lookup).node.children.Some?) {
      RefinesInterpretLookup(lookup, key);
    } else {
      if |lookup| == 1 {
        M.MergeIsAssociative(
            M.Update(M.NopDelta()),
            P.NodeLookup(lookup[0].node, key),
            M.DefineDefault());
        assert B.InterpretLookup(IReadOps(lookup), key)
            //== M.Merge(M.Update(M.NopDelta()), M.Merge(P.NodeLookup(lookup[0].node, key), M.DefineDefault()))
            //== M.Merge(M.Merge(M.Update(M.NopDelta()), P.NodeLookup(lookup[0].node, key)), M.DefineDefault())
            == M.Merge(P.InterpretLookup(lookup, key), M.DefineDefault())
            == P.InterpretLookupAccountingForLeaf(lookup, key);
      } else {
        forall idx | P.ValidLayerIndex(DropLast(lookup), idx) && idx < |DropLast(lookup)| - 1
        ensures P.LookupFollowsChildRefAtLayer(key, DropLast(lookup), idx)
        {
          assert P.LookupFollowsChildRefAtLayer(key, lookup, idx);
        }

        assert P.LookupFollowsChildRefAtLayer(key, lookup, |lookup|-2);
        RefinesInterpretLookup(DropLast(lookup), key);

        M.MergeIsAssociative(
            B.InterpretLookup(DropLast(IReadOps(lookup)), key),
            P.NodeLookup(Last(lookup).node, key),
            M.DefineDefault());
            /*
        assert B.InterpretLookup(IReadOps(lookup), key)
            == M.Merge(B.InterpretLookup(DropLast(IReadOps(lookup)), key), Last(IReadOps(lookup)).node.buffer[key])
            == M.Merge(B.InterpretLookup(DropLast(IReadOps(lookup)), key), M.Merge(P.NodeLookup(Last(lookup).node, key), M.DefineDefault()))
            == M.Merge(M.Merge(B.InterpretLookup(DropLast(IReadOps(lookup)), key), P.NodeLookup(Last(lookup).node, key)), M.DefineDefault())
            == P.InterpretLookupAccountingForLeaf(lookup, key);
            */
      }
    }
  }

  lemma RefinesValidQuery(q: P.LookupQuery)
  requires P.ValidQuery(q)
  ensures B.ValidQuery(IQuery(q))
  {
    RefinesLookup(q.lookup, q.key);
    RefinesInterpretLookupAccountingForLeaf(q.lookup, q.key, q.value);
  }

  lemma RefinesValidInsertion(ins: P.MessageInsertion)
  requires P.ValidInsertion(ins)
  ensures B.ValidInsertion(IInsertion(ins))
  {
  }

  lemma RefinesValidFlush(flush: P.NodeFlush)
  requires P.ValidFlush(flush)
  ensures B.ValidFlush(IFlush(flush))
  {
  }

  lemma RefinesValidGrow(growth: P.RootGrowth)
  requires P.ValidGrow(growth)
  ensures B.ValidGrow(IGrow(growth))
  {
  }

  lemma CutoffNodeAndKeepLeftAgree(node: PNode, node': PNode, pivot: Key, key: Key)
  requires P.WFNode(node)
  requires P.WFNode(node')
  requires node' == P.CutoffNodeAndKeepLeft(node, pivot);
  requires Keyspace.lt(key, pivot);
  ensures IBuffer(node)[key] == IBuffer(node')[key]
  ensures IMapsAgreeOnKey(IChildren(node), IChildren(node'), key)
  {
    P.reveal_CutoffNodeAndKeepLeft();
    var i := Route(node'.pivotTable, key);
    RouteIs(node.pivotTable, key, i);
  }

  lemma CutoffNodeAndKeepRightAgree(node: PNode, node': PNode, pivot: Key, key: Key)
  requires P.WFNode(node)
  requires P.WFNode(node')
  requires node' == P.CutoffNodeAndKeepRight(node, pivot);
  requires Keyspace.lte(pivot, key);
  ensures IBuffer(node)[key] == IBuffer(node')[key]
  ensures IMapsAgreeOnKey(IChildren(node), IChildren(node'), key)
  {
    P.reveal_CutoffNodeAndKeepRight();
    var i := Route(node'.pivotTable, key);
    RouteIs(node.pivotTable, key, i + |node.pivotTable| - |node'.pivotTable|);
  }

  lemma CutoffNodeAgree(node: PNode, node': PNode, l: Option<Key>, r: Option<Key>, key: Key)
  requires P.WFNode(node)
  requires P.WFNode(node')
  requires node' == P.CutoffNode(node, l, r);
  requires l.Some? ==> Keyspace.lte(l.value, key);
  requires r.Some? ==> Keyspace.lt(key, r.value);
  ensures IBuffer(node)[key] == IBuffer(node')[key]
  ensures IMapsAgreeOnKey(IChildren(node), IChildren(node'), key)
  {
    P.reveal_CutoffNode();
    if (l.Some?) {
      if (r.Some?) {
        var node1 := P.CutoffNodeAndKeepLeft(node, r.value);
        CutoffNodeAndKeepLeftAgree(node, node1, r.value, key);
        CutoffNodeAndKeepRightAgree(node1, node', l.value, key);
      } else {
        CutoffNodeAndKeepRightAgree(node, node', l.value, key);
      }
    } else {
      if (r.Some?) {
        CutoffNodeAndKeepLeftAgree(node, node', r.value, key);
      } else {
      }
    }
  }

  lemma WriteFusedChildInTermsOfLeftAndRight(l: PNode, r: PNode, child: PNode, pivot: Key, num_children_left: int)
  requires P.WFNode(l)
  requires P.WFNode(r)
  requires P.WFNode(child)
  requires 1 <= num_children_left < |child.buckets|
  requires l == P.G.Node(
      child.pivotTable[ .. num_children_left - 1 ],
      if child.children.Some? then Some(child.children.value[ .. num_children_left ]) else None,
      child.buckets[ .. num_children_left ]
    )
  requires r == P.G.Node(
      child.pivotTable[ num_children_left .. ],
      if child.children.Some? then Some(child.children.value[ num_children_left .. ]) else None,
      child.buckets[ num_children_left .. ]
    )
  requires child.pivotTable[num_children_left - 1] == pivot
  ensures child == P.G.Node(
      concat3(l.pivotTable, pivot, r.pivotTable),
      if l.children.Some? then Some(l.children.value + r.children.value) else None,
      l.buckets + r.buckets
    )
  {
    reveal_concat3();
    assert child.pivotTable == concat3(l.pivotTable, pivot, r.pivotTable);
    if (child.children.Some?) {
      assert child.children.value == child.children.value[..num_children_left] + child.children.value[num_children_left..];
      assert child.children == if l.children.Some? then Some(l.children.value + r.children.value) else None;
    } else {
      assert child.children == if l.children.Some? then Some(l.children.value + r.children.value) else None;
    }
    assert child.buckets == l.buckets + r.buckets;
  }

  lemma MergedNodeAndLeftAgree(l: PNode, r: PNode, node: PNode, pivot: Key, key: Key)
  requires P.WFNode(l)
  requires P.WFNode(r)
  requires P.WFNode(node)
  requires l.children.Some? <==> r.children.Some?
  requires node == P.G.Node(
      concat3(l.pivotTable, pivot, r.pivotTable),
      if l.children.Some? then Some(l.children.value + r.children.value) else None,
      l.buckets + r.buckets
    )
  requires Keyspace.lt(key, pivot);
  ensures IBuffer(l)[key] == IBuffer(node)[key]
  ensures IMapsAgreeOnKey(IChildren(l), IChildren(node), key)
  {
    var i := Route(l.pivotTable, key);
    RouteIs(node.pivotTable, key, i);
  }

  lemma MergedNodeAndRightAgree(l: PNode, r: PNode, node: PNode, pivot: Key, key: Key)
  requires P.WFNode(l)
  requires P.WFNode(r)
  requires P.WFNode(node)
  requires l.children.Some? <==> r.children.Some?
  requires node == P.G.Node(
      concat3(l.pivotTable, pivot, r.pivotTable),
      if l.children.Some? then Some(l.children.value + r.children.value) else None,
      l.buckets + r.buckets
    )
  requires Keyspace.lte(pivot, key);
  ensures IBuffer(r)[key] == IBuffer(node)[key]
  ensures IMapsAgreeOnKey(IChildren(r), IChildren(node), key)
  {
    var i := Route(r.pivotTable, key);
    if (i > 0) {
      assert node.pivotTable[i + |l.buckets| - 1] == r.pivotTable[i - 1];
    }
    if (i + |l.buckets| < |node.pivotTable|) {
      assert node.pivotTable[i + |l.buckets|] == r.pivotTable[i];
    }
    RouteIs(node.pivotTable, key, i + |l.buckets|);
  }

  lemma ValidLeftChildHasGoodPivots(f: P.NodeFusion)
  requires P.ValidSplit(f)
  ensures f.slot_idx > 0 && |f.left_child.pivotTable| > 0 ==> Keyspace.lt(f.split_parent.pivotTable[f.slot_idx-1], f.left_child.pivotTable[0])
  ensures |f.left_child.pivotTable| > 0 ==> Keyspace.lt(Last(f.left_child.pivotTable), f.split_parent.pivotTable[f.slot_idx])
  {
    Keyspace.reveal_IsStrictlySorted();
  }

  lemma ValidRightChildHasGoodPivots(f: P.NodeFusion)
  requires P.ValidSplit(f)
  ensures |f.right_child.pivotTable| > 0 ==> Keyspace.lt(f.split_parent.pivotTable[f.slot_idx], f.right_child.pivotTable[0])
  ensures f.slot_idx+1 < |f.split_parent.pivotTable| && |f.right_child.pivotTable| > 0 ==> Keyspace.lt(Last(f.right_child.pivotTable), f.split_parent.pivotTable[f.slot_idx+1])
  {
    Keyspace.reveal_IsStrictlySorted();
  }

  lemma ValidMergeChildHasGoodPivots(f: P.NodeFusion)
  requires P.ValidMerge(f)
  ensures f.slot_idx > 0 && |f.fused_child.pivotTable| > 0 ==> Keyspace.lt(f.fused_parent.pivotTable[f.slot_idx-1], f.fused_child.pivotTable[0])
  ensures f.slot_idx < |f.fused_parent.pivotTable| && |f.fused_child.pivotTable| > 0 ==> Keyspace.lt(Last(f.fused_child.pivotTable), f.fused_parent.pivotTable[f.slot_idx])
  {
    var lb := (if f.slot_idx > 0 then Some(f.split_parent.pivotTable[f.slot_idx - 1]) else None);
    var ub := (if f.slot_idx + 1 < |f.split_parent.pivotTable| then Some(f.split_parent.pivotTable[f.slot_idx + 1]) else None);
    var l := P.CutoffNode(f.left_child, lb , Some(f.pivot));
    var r := P.CutoffNode(f.right_child, Some(f.pivot), ub);

    if (f.slot_idx > 0 && |f.fused_child.pivotTable| > 0) {
      assert f.fused_parent.pivotTable[f.slot_idx - 1] == f.split_parent.pivotTable[f.slot_idx - 1];
      if (|l.pivotTable| > 0) {
        assert f.fused_child.pivotTable[0] == l.pivotTable[0];
        assert Keyspace.lt(f.fused_parent.pivotTable[f.slot_idx-1], f.fused_child.pivotTable[0]);
      } else {
        assert f.fused_child.pivotTable[0] == f.pivot;
        Keyspace.IsStrictlySortedImpliesLt(f.split_parent.pivotTable, f.slot_idx - 1, f.slot_idx);
        assert Keyspace.lt(f.fused_parent.pivotTable[f.slot_idx-1], f.fused_child.pivotTable[0]);
      }
    }

    if (f.slot_idx < |f.fused_parent.pivotTable| && |f.fused_child.pivotTable| > 0) {
      assert f.fused_parent.pivotTable[f.slot_idx] == f.split_parent.pivotTable[f.slot_idx + 1];
      if (|r.pivotTable| > 0) {
        assert Last(f.fused_child.pivotTable) == Last(r.pivotTable);
        assert Keyspace.lt(Last(f.fused_child.pivotTable), f.fused_parent.pivotTable[f.slot_idx]);
      } else {
        assert Last(f.fused_child.pivotTable) == f.pivot;
        Keyspace.IsStrictlySortedImpliesLt(f.split_parent.pivotTable, f.slot_idx, f.slot_idx + 1);
        assert Keyspace.lt(Last(f.fused_child.pivotTable), f.fused_parent.pivotTable[f.slot_idx]);
      }
    }

  }

  lemma SplitMergeBuffersChildrenEq(node: PNode, node': PNode, idx: int)
  requires P.WFNode(node)
  requires P.WFNode(node')
  requires |node'.buckets| == |node.buckets| + 1
  requires 0 <= idx < |node.buckets|
  requires forall i | 0 <= i < idx :: node.buckets[i] == node'.buckets[i]
  requires node.buckets[idx] == map[]
  requires node'.buckets[idx] == map[]
  requires node'.buckets[idx+1] == map[]
  requires forall i | idx + 2 <= i < |node'.buckets| :: node'.buckets[i] == node.buckets[i-1]
  requires forall i | 0 <= i < idx :: node.pivotTable[i] == node'.pivotTable[i]
  requires forall i | idx < i < |node'.pivotTable| :: node'.pivotTable[i] == node.pivotTable[i-1]
  requires node.children.Some?
  requires node'.children.Some?
  requires forall i | 0 <= i < idx :: node.children.value[i] == node'.children.value[i]
  requires forall i | idx + 2 <= i < |node'.buckets| :: node'.children.value[i] == node.children.value[i-1]
  ensures IBuffer(node) == IBuffer(node')
  ensures forall key | key !in PivotTableBucketKeySet(node.pivotTable, idx) ::
      IChildren(node)[key] == IChildren(node')[key]
  {
    forall key
    ensures IBuffer(node)[key] == IBuffer(node')[key]
    ensures key !in PivotTableBucketKeySet(node.pivotTable, idx) ==> IChildren(node)[key] == IChildren(node')[key]

    {
      var i := Route(node'.pivotTable, key);
      if (i < idx) {
        RouteIs(node.pivotTable, key, i);
        assert node'.buckets[i] == node.buckets[i];
        assert IBuffer(node)[key] == IBuffer(node')[key];
        assert IChildren(node)[key] == IChildren(node')[key];
      } else if (i == idx) {
        if (idx < |node.pivotTable|) {
          assert node'.pivotTable[idx+1] == node.pivotTable[idx];
        }
        RouteIs(node.pivotTable, key, idx);
        assert node'.buckets[i] == map[];
        assert node.buckets[i] == map[];
        assert IBuffer(node)[key] == IBuffer(node')[key];
        assert key in PivotTableBucketKeySet(node.pivotTable, idx);
      } else if (i == idx + 1) {
        if (idx + 1 < |node'.pivotTable|) {
          assert node'.pivotTable[idx+1] == node.pivotTable[idx];
        }
        RouteIs(node.pivotTable, key, idx);
        assert node'.buckets[i] == map[];
        assert node.buckets[idx] == map[];
        assert IBuffer(node)[key] == IBuffer(node')[key];
        assert key in PivotTableBucketKeySet(node.pivotTable, idx);
      } else {
        if i - 1 > 0 {
          assert node.pivotTable[i-2] == node'.pivotTable[i-1];
        }
        if i - 1 < |node.pivotTable| {
          assert node.pivotTable[i-1] == node'.pivotTable[i];
        }
        RouteIs(node.pivotTable, key, i - 1);
        assert node'.buckets[i] == node.buckets[i-1];
        assert IBuffer(node)[key] == IBuffer(node')[key];
        assert IChildren(node)[key] == IChildren(node')[key];
      }
    }
  }

  lemma RefinesValidMerge(f: P.NodeFusion)
  requires P.ValidMerge(f)
  ensures B.ValidRedirect(IMerge(f))
  {
    assert P.WFNode(f.split_parent);
    assert P.WFNode(f.left_child);
    assert P.WFNode(f.right_child);
    var redirect := IMerge(f);
    PivotBetreeSpecWFNodes.ValidMergeWritesWFNodes(f);

    assert P.WFNode(P.MergeOps(f)[0].node);
    assert P.WFNode(P.MergeOps(f)[1].node);

    forall ref | ref in IMapRestrict(redirect.old_parent.children, redirect.keys).Values
    ensures ref in redirect.old_childrefs
    {
      var key :| IMapsTo(IMapRestrict(redirect.old_parent.children, redirect.keys), key, ref);
      assert key in redirect.keys;
      if (Keyspace.lt(key, f.pivot)) {
        RouteIs(f.split_parent.pivotTable, key, f.slot_idx);
        assert ref == f.left_childref;
      } else {
        if f.slot_idx + 1 < |f.split_parent.pivotTable| {
          assert f.split_parent.pivotTable[f.slot_idx + 1] == f.fused_parent.pivotTable[f.slot_idx];
        }
        RouteIs(f.split_parent.pivotTable, key, f.slot_idx + 1);
        assert ref == f.right_childref;
      }
    }

    forall ref | ref in redirect.old_childrefs
    ensures ref in IMapRestrict(redirect.old_parent.children, redirect.keys).Values
    {
      assert ref == f.left_childref || ref == f.right_childref;
      if (ref == f.left_childref) {
        var key := GetKeyInBucket(f.split_parent.pivotTable, f.slot_idx);
        RouteIs(f.fused_parent.pivotTable, key, f.slot_idx);
        assert key in redirect.keys;
        assert key in IMapRestrict(redirect.old_parent.children, redirect.keys);
        assert IMapRestrict(redirect.old_parent.children, redirect.keys)[key] == ref;
        assert ref in IMapRestrict(redirect.old_parent.children, redirect.keys).Values;
      } else {
        var key := GetKeyInBucket(f.split_parent.pivotTable, f.slot_idx + 1);
        RouteIs(f.fused_parent.pivotTable, key, f.slot_idx);
        assert key in redirect.keys;
        assert key in IMapRestrict(redirect.old_parent.children, redirect.keys);
        assert IMapRestrict(redirect.old_parent.children, redirect.keys)[key] == ref;
        assert ref in IMapRestrict(redirect.old_parent.children, redirect.keys).Values;
      }
    }

    SplitMergeBuffersChildrenEq(f.fused_parent, f.split_parent, f.slot_idx);

    var lb := (if f.slot_idx > 0 then Some(f.split_parent.pivotTable[f.slot_idx - 1]) else None);
    var ub := (if f.slot_idx + 1 < |f.split_parent.pivotTable| then Some(f.split_parent.pivotTable[f.slot_idx + 1]) else None);
    var l := P.CutoffNode(f.left_child, lb , Some(f.pivot));
    var r := P.CutoffNode(f.right_child, Some(f.pivot), ub);

    assert redirect.old_children[f.left_childref] == INode(f.left_child);
    assert redirect.old_children[f.right_childref] == INode(f.right_child);

    forall key | key in redirect.keys * redirect.old_parent.children.Keys
    ensures redirect.old_parent.children[key] in redirect.old_children
    ensures IMapsAgreeOnKey(redirect.new_children[redirect.new_parent.children[key]].buffer, redirect.old_children[redirect.old_parent.children[key]].buffer, key)
    ensures IMapsAgreeOnKey(redirect.new_children[redirect.new_parent.children[key]].children, redirect.old_children[redirect.old_parent.children[key]].children, key)
    {
      assert key in redirect.keys;
      if (Keyspace.lt(key, f.pivot)) {
        RouteIs(f.split_parent.pivotTable, key, f.slot_idx);
        assert redirect.old_parent.children[key] == f.left_childref;
        assert redirect.old_children[redirect.old_parent.children[key]] == INode(f.left_child);
        CutoffNodeAgree(f.left_child, l, lb, Some(f.pivot), key);
        MergedNodeAndLeftAgree(l, r, f.fused_child, f.pivot, key);
      } else {
        if f.slot_idx + 1 < |f.split_parent.pivotTable| {
          assert f.split_parent.pivotTable[f.slot_idx + 1] == f.fused_parent.pivotTable[f.slot_idx];
        }
        RouteIs(f.split_parent.pivotTable, key, f.slot_idx + 1);
        assert redirect.old_parent.children[key] == f.right_childref;
        assert redirect.old_children[redirect.old_parent.children[key]] == INode(f.right_child);
        CutoffNodeAgree(f.right_child, r, Some(f.pivot), ub, key);
        MergedNodeAndRightAgree(l, r, f.fused_child, f.pivot, key);
      }
    }

    forall childref, ref | childref in redirect.new_children && ref in redirect.new_children[childref].children.Values
    ensures exists key ::
          && IMapsTo(redirect.new_parent.children, key, childref)
          && IMapsTo(redirect.new_children[childref].children, key, ref)
          && key in redirect.keys
          && key in redirect.old_parent.children
    {
      assert childref == f.fused_childref;
      var new_child := redirect.new_children[childref];
      var key :| key in new_child.children && new_child.children[key] == ref;
      var i := Route(f.fused_child.pivotTable, key);
      ValidMergeChildHasGoodPivots(f);
      var key1 := GetKeyInChildBucket(f.fused_parent.pivotTable, f.fused_child.pivotTable, f.slot_idx, i);
      assert key1 in redirect.keys;
      assert key1 in redirect.old_parent.children.Keys;
      assert new_child.children[key1] == ref;
      assert key1 in redirect.keys * redirect.old_parent.children.Keys;
      assert key1 in IMapRestrict(new_child.children, redirect.keys * redirect.old_parent.children.Keys);

      assert IMapsTo(redirect.new_parent.children, key1, childref)
          && IMapsTo(redirect.new_children[childref].children, key1, ref)
          && key1 in redirect.keys
          && key1 in redirect.old_parent.children;
    }
  }

  lemma RefinesValidSplit(f: P.NodeFusion)
  requires P.ValidSplit(f)
  ensures B.ValidRedirect(ISplit(f))
  {
    var r := ISplit(f);
    PivotBetreeSpecWFNodes.ValidSplitWritesWFNodes(f);

    forall ref | ref in IMapRestrict(r.old_parent.children, r.keys).Values
    ensures ref in r.old_childrefs
    {
      //var key :| key in IMapRestrict(r.old_parent.children, r.keys) && IMapRestrict(r.old_parent.children, r.keys)[key] == ref;
      //assert key in r.keys;
      //assert Route(f.fused_parent.pivotTable, key) == f.slot_idx;
      //assert ref == f.fused_childref;
    }

    forall ref | ref in r.old_childrefs
    ensures ref in IMapRestrict(r.old_parent.children, r.keys).Values
    {
      assert ref == f.fused_childref;
      var key := GetKeyInBucket(f.fused_parent.pivotTable, f.slot_idx);
      assert IMapRestrict(r.old_parent.children, r.keys)[key] == ref;
    }

    SplitMergeBuffersChildrenEq(f.fused_parent, f.split_parent, f.slot_idx);

    var lbound := (if f.slot_idx > 0 then Some(f.fused_parent.pivotTable[f.slot_idx - 1]) else None);
    var ubound := (if f.slot_idx < |f.fused_parent.pivotTable| then Some(f.fused_parent.pivotTable[f.slot_idx]) else None);
    var ch := P.CutoffNode(f.fused_child, lbound, ubound);

    forall key | key in r.keys * r.old_parent.children.Keys
    ensures r.old_parent.children[key] in r.old_children
    ensures r.new_parent.children[key] in r.new_children
    ensures IMapsAgreeOnKey(
          r.new_children[r.new_parent.children[key]].buffer,
          r.old_children[r.old_parent.children[key]].buffer,
          key)
    ensures IMapsAgreeOnKey(
          r.new_children[r.new_parent.children[key]].children,
          r.old_children[r.old_parent.children[key]].children,
          key)
    {
      CutoffNodeAgree(f.fused_child, ch, lbound, ubound, key);

      assert key in r.keys;
      if (Keyspace.lt(key, f.pivot)) {
        RouteIs(f.split_parent.pivotTable, key, f.slot_idx);
        assert r.new_parent.children[key] == f.left_childref;
        assert r.new_children[r.new_parent.children[key]] == INode(f.left_child);
        WriteFusedChildInTermsOfLeftAndRight(f.left_child, f.right_child, ch, f.pivot, f.num_children_left);
        MergedNodeAndLeftAgree(f.left_child, f.right_child, ch, f.pivot, key);
      } else {
        if f.slot_idx + 1 < |f.split_parent.pivotTable| {
          assert f.split_parent.pivotTable[f.slot_idx + 1] == f.fused_parent.pivotTable[f.slot_idx];
        }
        RouteIs(f.split_parent.pivotTable, key, f.slot_idx + 1);
        assert r.new_parent.children[key] == f.right_childref;
        assert r.new_children[r.new_parent.children[key]] == INode(f.right_child);
        WriteFusedChildInTermsOfLeftAndRight(f.left_child, f.right_child, ch, f.pivot, f.num_children_left);
        MergedNodeAndRightAgree(f.left_child, f.right_child, ch, f.pivot, key);
      }
    }

    forall childref, ref | childref in r.new_children && ref in r.new_children[childref].children.Values
    ensures exists key ::
          && IMapsTo(r.new_parent.children, key, childref)
          && IMapsTo(r.new_children[childref].children, key, ref)
          && key in r.keys
          && key in r.old_parent.children
    {
      var new_child := r.new_children[childref];
      var key :| key in new_child.children && new_child.children[key] == ref;

      var parent_slot;
      var lr_child;
      if (childref == f.left_childref) {
        parent_slot := f.slot_idx;
        lr_child := f.left_child;
      } else {
        parent_slot := f.slot_idx + 1;
        lr_child := f.right_child;
      }
      var child_slot := Route(lr_child.pivotTable, key);
      ValidLeftChildHasGoodPivots(f);
      ValidRightChildHasGoodPivots(f);
      var key1 := GetKeyInChildBucket(f.split_parent.pivotTable, lr_child.pivotTable, parent_slot, child_slot);
        
      assert IMapsTo(r.new_parent.children, key1, childref);

      assert IMapsTo(r.new_children[childref].children, key1, ref);
      assert key1 in r.keys;
      assert key1 in r.old_parent.children;
    }

  }

  lemma RefinesValidBetreeStep(betreeStep: P.BetreeStep)
  requires P.ValidBetreeStep(betreeStep)
  requires !betreeStep.BetreeRepivot?
  ensures B.ValidBetreeStep(IStep(betreeStep))
  {
    match betreeStep {
      case BetreeQuery(q) => RefinesValidQuery(q);
      case BetreeInsert(ins) => RefinesValidInsertion(ins);
      case BetreeFlush(flush) => RefinesValidFlush(flush);
      case BetreeGrow(growth) => RefinesValidGrow(growth);
      case BetreeSplit(fusion) => RefinesValidSplit(fusion);
      case BetreeMerge(fusion) => RefinesValidMerge(fusion);
    }
  }

  lemma {:fuel IReadOps,3} RefinesReadOps(betreeStep: P.BetreeStep)
  requires P.ValidBetreeStep(betreeStep)
  requires !betreeStep.BetreeRepivot?
  ensures B.ValidBetreeStep(IStep(betreeStep))
  ensures IReadOps(P.BetreeStepReads(betreeStep)) == B.BetreeStepReads(IStep(betreeStep))
  {
    RefinesValidBetreeStep(betreeStep);
    /*
    match betreeStep {
      case BetreeInsert(ins) => {
        assert IReadOps(P.BetreeStepReads(betreeStep)) == B.BetreeStepReads(IStep(betreeStep));
      }
      case BetreeFlush(flush) => {
        assert IReadOps(P.BetreeStepReads(betreeStep)) == B.BetreeStepReads(IStep(betreeStep));
      }
      case BetreeGrow(growth) => {
        assert IReadOps(P.BetreeStepReads(betreeStep))
            == IReadOps([P.G.ReadOp(P.G.Root(), growth.oldroot)])
            == [B.G.ReadOp(P.G.Root(), INode(growth.oldroot))]
            == B.BetreeStepReads(IStep(betreeStep));
      }
      case BetreeSplit(fusion) => {
        assert IReadOps(P.BetreeStepReads(betreeStep)) == B.BetreeStepReads(IStep(betreeStep));
      }
      case BetreeMerge(fusion) => {
        assert IReadOps(P.BetreeStepReads(betreeStep)) == B.BetreeStepReads(IStep(betreeStep));
      }
    }
    */
  }

  function IOp(op: P.G.Op) : B.G.Op
  requires P.WFNode(op.node)
  {
    match op {
      case AllocOp(ref, block) => B.G.AllocOp(ref, INode(block))
      case WriteOp(ref, block) => B.G.WriteOp(ref, INode(block))
    }
  }

  function IOps(ops: seq<P.G.Op>) : seq<B.G.Op>
  requires forall i | 0 <= i < |ops| :: P.WFNode(ops[i].node)
  {
    if |ops| == 0 then [] else
      IOps(ops[..|ops|-1]) + [IOp(ops[|ops|-1])]
  }

  lemma InsertRefinesOps(ins: P.MessageInsertion)
  requires P.ValidInsertion(ins)
  requires B.ValidInsertion(IInsertion(ins))
  ensures forall i | 0 <= i < |P.InsertionOps(ins)| ::
      P.WFNode(P.InsertionOps(ins)[i].node)
  ensures IOps(P.InsertionOps(ins)) == B.InsertionOps(IInsertion(ins))
  {
    var newroot := P.AddMessageToNode(ins.oldroot, ins.key, ins.msg);
    var newroot' := B.AddMessageToNode(INode(ins.oldroot), ins.key, ins.msg);

    forall key
    ensures INode(newroot).buffer[key] == newroot'.buffer[key]
    {
      if (key == ins.key) {
        var oldroot := ins.oldroot;
        var oldroot' := IInsertion(ins).oldroot;
        // IBuffer splits into cases based on whether a node is a leaf
        // so we have to split into cases here.
        if (oldroot.children.Some?) {
          assert INode(newroot).buffer[key] == newroot'.buffer[key];
        } else {
          M.MergeIsAssociative(
            ins.msg,
            P.BucketLookup(oldroot.buckets[Route(oldroot.pivotTable, ins.key)], ins.key),
            M.DefineDefault()
          );
          assert INode(newroot).buffer[key] == newroot'.buffer[key];
        }
      } else {
        assert INode(newroot).buffer[key] == newroot'.buffer[key];
      }
    }

    assert INode(newroot).children == newroot'.children;
    assert INode(newroot).buffer == newroot'.buffer;

    assert INode(newroot) == newroot';
  }

  lemma AddMessagesToBucketsResult(
      pivotTable: PivotTable,
      i: int,
      buckets: seq<map<Key, M.Message>>,
      parentBucket: map<Key, M.Message>,
      key: Key)
  requires WFPivots(pivotTable)
  requires 0 <= i <= |buckets|;
  ensures key !in parentBucket && Route(pivotTable, key) < i ==>
      P.BucketLookup(P.AddMessagesToBuckets(pivotTable, i, buckets, parentBucket)[Route(pivotTable, key)], key)
   == P.BucketLookup(buckets[Route(pivotTable, key)], key)
  ensures key in parentBucket && Route(pivotTable, key) < i ==>
      P.BucketLookup(P.AddMessagesToBuckets(pivotTable, i, buckets, parentBucket)[Route(pivotTable, key)], key)
   == M.Merge(parentBucket[key],
      P.BucketLookup(buckets[Route(pivotTable, key)], key))
  {
    if (i == 0) {
    } else {
      AddMessagesToBucketsResult(pivotTable, i-1, buckets, parentBucket, key);
    }
  }

  lemma AddMessagesToNodeResult(node: PNode, bucket: map<Key, M.Message>, node': PNode, key: Key)
  requires P.WFNode(node)
  requires node' == P.AddMessagesToNode(node, bucket);
  ensures key !in bucket ==> P.NodeLookup(node', key) == P.NodeLookup(node, key)
  ensures key in bucket ==> P.NodeLookup(node', key) == M.Merge(bucket[key], P.NodeLookup(node, key))
  {
    AddMessagesToBucketsResult(node.pivotTable, |node.buckets|, node.buckets, bucket, key);
  }

  lemma {:fuel IOps,2} FlushRefinesOps(flush: P.NodeFlush)
  requires P.ValidFlush(flush)
  requires B.ValidFlush(IFlush(flush))
  ensures forall i | 0 <= i < |P.FlushOps(flush)| ::
      P.WFNode(P.FlushOps(flush)[i].node)
  ensures IOps(P.FlushOps(flush)) == B.FlushOps(IFlush(flush))
  {
    var newparent := P.G.Node(
        flush.parent.pivotTable,
        Some(flush.parent.children.value[flush.slotIndex := flush.newchildref]),
        flush.parent.buckets[flush.slotIndex := map[]]
      );
    var bucket := flush.parent.buckets[flush.slotIndex];
    var newchild := P.AddMessagesToNode(flush.child, bucket);
    var allocop := P.G.AllocOp(flush.newchildref, newchild);
    var writeop := P.G.WriteOp(flush.parentref, newparent);

    /*
    assert |newchild.buckets| == |flush.child.buckets|;
    assert |newchild.pivotTable| == |flush.child.pivotTable|;
    assert P.WFNode(newchild);
    assert P.WFNode(newparent);
    */

    var flush' := IFlush(flush);
    var parentref := flush'.parentref;
    var parent := flush'.parent;
    var childref := flush'.childref;
    var child := flush'.child;
    var newchildref := flush'.newchildref;
    var newbuffer := imap k :: (if k in flush'.movedKeys then B.G.M.Merge(parent.buffer[k], child.buffer[k]) else child.buffer[k]);
    var newchild' := B.G.Node(child.children, newbuffer);
    var newparentbuffer := imap k :: (if k in flush'.movedKeys then B.G.M.Update(B.G.M.NopDelta()) else parent.buffer[k]);
    var newparentchildren := imap k | k in parent.children :: (if k in flush'.movedKeys then newchildref else parent.children[k]);
    var newparent' := B.G.Node(newparentchildren, newparentbuffer);
    var allocop' := B.G.AllocOp(newchildref, newchild');
    var writeop' := B.G.WriteOp(parentref, newparent');

    forall k: Key
    ensures IBuffer(newchild)[k] == newbuffer[k]
    {
      AddMessagesToNodeResult(flush.child, bucket, newchild, k);
      if (k in flush'.movedKeys) {
        //RouteIs(flush.parent.pivotTable, k, flush.slotIndex);
        if (newchild.children.Some?) {
          assert IBuffer(newchild)[k] == newbuffer[k];
        } else {
          M.MergeIsAssociative(P.BucketLookup(bucket, k), P.NodeLookup(flush.child, k), M.DefineDefault());
          /*
          assert IBuffer(newchild)[k]
              == M.Merge(P.NodeLookup(newchild, k), M.DefineDefault())
              == M.Merge(M.Merge(P.BucketLookup(bucket, k), P.NodeLookup(flush.child, k)), M.DefineDefault())
              == M.Merge(P.BucketLookup(bucket, k), M.Merge(P.NodeLookup(flush.child, k), M.DefineDefault()))
              == newbuffer[k];*/
        }
      } else {
        assert P.NodeHasWFBucketAt(flush.parent, flush.slotIndex);
        //assert k !in bucket;
        /*
        if (newchild.children.Some?) {
          assert flush.child.children.Some?;
          assert IBuffer(newchild)[k] == IBuffer(flush.child)[k];
        } else {
          assert flush.child.children.None?;
          assert IBuffer(newchild)[k] == IBuffer(flush.child)[k];
        }
        */
        assert IBuffer(newchild)[k] == newbuffer[k];
      }
    }

    forall i | 0 <= i < |newparent.buckets|
    ensures P.NodeHasWFBucketAt(newparent, i)
    {
      assert P.NodeHasWFBucketAt(flush.parent, i);
    }
    //assert P.WFNode(newparent);

    //assert IChildren(newchild) == newchild'.children;
    //assert IBuffer(newchild) == newbuffer;

    /*
    forall k: Key
    ensures IChildren(newparent)[k] == newparent'.children[k]
    {
      if (k in flush'.movedKeys) {
        RouteIs(flush.parent.pivotTable, k, flush.slotIndex);
        assert IChildren(newparent)[k] == newparent'.children[k];
      } else {
        assert IChildren(newparent)[k] == newparent'.children[k];
      }
    }
    */

    /*
    assert IChildren(newparent) == newparent'.children;
    assert IBuffer(newparent) == newparentbuffer;

    assert INode(newchild) == newchild';
    assert INode(newparent) == newparent';
    */

    assert IOp(allocop) == allocop';
    assert IOp(writeop) == writeop';
  }

  lemma {:fuel IOps,3} GrowRefinesOps(growth: P.RootGrowth)
  requires P.ValidGrow(growth)
  requires B.ValidGrow(IGrow(growth))
  ensures forall i | 0 <= i < |P.GrowOps(growth)| ::
      P.WFNode(P.GrowOps(growth)[i].node)
  ensures IOps(P.GrowOps(growth)) == B.GrowOps(IGrow(growth))
  {
    var newroot := P.G.Node([], Some([growth.newchildref]), [map[]]);
    var newroot' := B.G.Node(
        imap key | MS.InDomain(key) :: IGrow(growth).newchildref,
        imap key | MS.InDomain(key) :: B.G.M.Update(B.G.M.NopDelta()));
    assert INode(newroot) == newroot';
    //assert INode(growth.oldroot) == IGrow(growth).oldroot;

    //assert B.GrowOps(IGrow(growth))[0] 
    //    == B.G.AllocOp(IGrow(growth).newchildref, IGrow(growth).oldroot);

    // observe: (I don't know really know why this is necessary)
    assert B.GrowOps(IGrow(growth))[1] 
        == B.G.WriteOp(B.G.Root(), newroot');

    /*
    assert IOps(P.GrowOps(growth))
        == IOps([P.G.AllocOp(growth.newchildref, growth.oldroot), P.G.WriteOp(P.G.Root(), newroot)])
        == [B.G.AllocOp(growth.newchildref, INode(growth.oldroot)), B.G.WriteOp(B.G.Root(), INode(newroot))]
        == [B.G.AllocOp(IGrow(growth).newchildref, IGrow(growth).oldroot), B.G.WriteOp(B.G.Root(), newroot')]
        == B.GrowOps(IGrow(growth));
    */
  }

  lemma {:fuel IOps,3} SplitRefinesOps(f: P.NodeFusion)
  requires P.ValidSplit(f)
  requires B.ValidRedirect(ISplit(f))
  ensures forall i | 0 <= i < |P.SplitOps(f)| ::
      P.WFNode(P.SplitOps(f)[i].node)
  ensures IOps(P.SplitOps(f)) == B.RedirectOps(ISplit(f))
  {
    PivotBetreeSpecWFNodes.ValidSplitWritesWFNodes(f);
    //assert IOp(P.G.AllocOp(f.left_childref, f.left_child)) == B.RedirectOps(ISplit(f))[0];
    //assert IOp(P.G.AllocOp(f.right_childref, f.right_child)) == B.RedirectOps(ISplit(f))[1];
    //assert IOp(P.G.WriteOp(f.parentref, f.split_parent)) == B.RedirectOps(ISplit(f))[2];

    /*
    assert IOps(P.SplitOps(f)) == [
      IOp(P.G.AllocOp(f.left_childref, f.left_child)),
      IOp(P.G.AllocOp(f.right_childref, f.right_child)),
      IOp(P.G.WriteOp(f.parentref, f.split_parent))
    ];

    assert IOps(P.SplitOps(f))
        == [
          IOp(P.G.AllocOp(f.left_childref, f.left_child)),
          IOp(P.G.AllocOp(f.right_childref, f.right_child)),
          IOp(P.G.WriteOp(f.parentref, f.split_parent))
        ]
        == [
          B.RedirectOps(ISplit(f))[0],
          B.RedirectOps(ISplit(f))[1],
          B.RedirectOps(ISplit(f))[2]
        ]
        == B.RedirectOps(ISplit(f));
        */
  }

  lemma {:fuel IOps,3} MergeRefinesOps(f: P.NodeFusion)
  requires P.ValidMerge(f)
  requires B.ValidRedirect(IMerge(f))
  ensures forall i | 0 <= i < |P.MergeOps(f)| ::
      P.WFNode(P.MergeOps(f)[i].node)
  ensures IOps(P.MergeOps(f)) == B.RedirectOps(IMerge(f))
  {
    PivotBetreeSpecWFNodes.ValidMergeWritesWFNodes(f);
  }

  lemma {:fuel IOps,3} RefinesOps(betreeStep: P.BetreeStep)
  requires P.ValidBetreeStep(betreeStep)
  requires !betreeStep.BetreeRepivot?
  ensures B.ValidBetreeStep(IStep(betreeStep))
  ensures forall i | 0 <= i < |P.BetreeStepOps(betreeStep)| ::
      P.WFNode(P.BetreeStepOps(betreeStep)[i].node)
  ensures IOps(P.BetreeStepOps(betreeStep)) == B.BetreeStepOps(IStep(betreeStep))
  {
    RefinesValidBetreeStep(betreeStep);

    match betreeStep {
      case BetreeQuery(q) => {
        assert forall i | 0 <= i < |P.BetreeStepOps(betreeStep)| ::
            P.WFNode(P.BetreeStepOps(betreeStep)[i].node);
        assert IOps(P.BetreeStepOps(betreeStep)) == B.BetreeStepOps(IStep(betreeStep));
      }
      case BetreeInsert(ins) => {
        InsertRefinesOps(ins);
      }
      case BetreeFlush(flush) => {
        FlushRefinesOps(flush);
      }
      case BetreeGrow(growth) => {
        GrowRefinesOps(growth);
      }
      case BetreeSplit(fusion) => {
        SplitRefinesOps(fusion);
      }
      case BetreeMerge(fusion) => {
        MergeRefinesOps(fusion);
      }
    }
  }

  lemma KeyInJoinedBucketsInSomeBucket(buckets: seq<P.G.Bucket>, key: Key)
  returns (i : int)
  requires key in P.JoinBuckets(buckets)
  ensures 0 <= i < |buckets|
  ensures key in buckets[i]
  {
    assert |buckets| > 0;
    if key in Last(buckets) {
      i := |buckets| - 1;
    } else {
      i := KeyInJoinedBucketsInSomeBucket(DropLast(buckets), key);
    }
  }

  lemma BucketLookupEqJoinLookup(buckets: seq<P.G.Bucket>, pivots: seq<Key>, key: Key)
  requires WFPivots(pivots)
  requires |buckets| == |pivots| + 1
  requires forall i | 0 <= i < |buckets| :: P.WFBucket(buckets[i], pivots, i)
  ensures P.BucketLookup(buckets[Route(pivots, key)], key) == P.BucketLookup(P.JoinBuckets(buckets), key);
  {
    if |pivots| == 0 {
      assert P.BucketLookup(buckets[Route(pivots, key)], key) == P.BucketLookup(P.JoinBuckets(buckets), key);
    } else {
      var b1 := P.JoinBuckets(DropLast(buckets));
      var b2 := Last(buckets);

      var piv := Last(pivots);
      WFSlice(pivots, 0, |pivots| - 1);

      forall i | 0 <= i < |DropLast(buckets)| ensures P.WFBucket(DropLast(buckets)[i], DropLast(pivots), i)
      {
        var bucket := DropLast(buckets)[i];
        assert P.WFBucket(buckets[i], pivots, i);
        forall key | key in bucket ensures Route(DropLast(pivots), key) == i {
          RouteIs(DropLast(pivots), key, i);
        }
      }

      BucketLookupEqJoinLookup(DropLast(buckets), DropLast(pivots), key);


      if Keyspace.lt(key, piv) {
        assert P.WFBucket(buckets[|buckets| - 1], pivots, |buckets| - 1);
        //if (key in b2) {
        //  assert Keyspace.lte(piv, key);
        //  assert false;
        //}
        assert key !in b2;
        assert P.BucketLookup(buckets[Route(pivots, key)], key) == P.BucketLookup(P.JoinBuckets(buckets), key);
      } else {
        if (key in b1) {
          var i := KeyInJoinedBucketsInSomeBucket(DropLast(buckets), key);
          assert false;
        }
        assert key !in b1;
        assert P.BucketLookup(buckets[Route(pivots, key)], key) == P.BucketLookup(P.JoinBuckets(buckets), key);
      }
    }
  }

  lemma IBufferLeafEqJoin(node: PNode)
  requires P.WFNode(node)
  ensures IBufferLeaf(node) == imap key :: M.Merge(P.BucketLookup(P.JoinBuckets(node.buckets), key), M.DefineDefault())
  {
    forall key
    ensures IBufferLeaf(node)[key] == M.Merge(P.BucketLookup(P.JoinBuckets(node.buckets), key), M.DefineDefault())
    {
      forall i | 0 <= i < |node.buckets| ensures P.WFBucket(node.buckets[i], node.pivotTable, i)
      {
        assert P.NodeHasWFBucketAt(node, i);
      }
      BucketLookupEqJoinLookup(node.buckets, node.pivotTable, key);
      //assert P.BucketLookup(node.buckets[Route(node.pivotTable, key)], key) == P.BucketLookup(P.JoinBuckets(node.buckets), key);
    }
  }

  lemma RepivotPreservesNode(r: P.Repivot)
  requires P.ValidRepivot(r)
  ensures P.WFNode(P.ApplyRepivot(r.leaf, r.pivots))
  ensures INode(r.leaf) == INode(P.ApplyRepivot(r.leaf, r.pivots))
  {
    PivotBetreeSpecWFNodes.WFApplyRepivot(r.leaf, r.pivots);

    var buckets1 := r.leaf.buckets;
    var joined := P.JoinBuckets(buckets1);
    var buckets2 := P.SplitBucketOnPivots(r.pivots, joined);

    forall i | 0 <= i < |buckets1|
    ensures forall key | key in buckets1[i] :: buckets1[i][key] != M.IdentityMessage()
    {
      assert P.NodeHasWFBucketAt(r.leaf, i);
    }
    PivotBetreeSpecWFNodes.JoinBucketsNoIdentity(r.leaf.buckets);
    PivotBetreeSpecWFNodes.SplitBucketOnPivotsCorrect(r.pivots, joined, buckets2);
    assert P.JoinBuckets(buckets1) == P.JoinBuckets(buckets2);
    
    IBufferLeafEqJoin(r.leaf);
    IBufferLeafEqJoin(P.ApplyRepivot(r.leaf, r.pivots));
  }
}
