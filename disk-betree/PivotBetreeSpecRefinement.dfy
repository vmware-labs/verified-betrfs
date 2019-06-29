include "BlockInterface.dfy"  
include "../lib/sequences.dfy"
include "../lib/Maps.dfy"
include "MapSpec.dfy"
include "Graph.dfy"
include "../tla-tree/MissingLibrary.dfy"
include "Message.dfy"
include "BetreeSpec.dfy"
include "Betree.dfy"
include "BetreeInv.dfy"
include "PivotBetreeSpec.dfy"

abstract module PivotBetreeSpecRefinement {
  import B = BetreeSpec`Internal
  import P = PivotBetreeSpec`Internal
  import M = Message
  import MS = MapSpec
  import Keyspace = MS.Keyspace
  import opened Maps
  import opened Sequences
  import opened MissingLibrary

  type Node = B.G.Node
  type PNode = P.G.Node

  type Key = B.G.Key
  type Value = B.G.Value
  type Reference = B.G.Reference
  type Buffer = B.G.Buffer
  type PivotTable = P.G.PivotTable

  function IChildren(node: PNode) : imap<Key, Reference>
  requires P.WFNode(node);
  {
    if node.children.Some? then (
      imap key :: node.children.value[P.Route(node.pivotTable, key)]
    ) else (
      imap[]
    )
  }

  function IBufferInternal(node: PNode) : Buffer
  requires P.WFNode(node);
  {
    imap key :: P.BucketLookup(node.buckets[P.Route(node.pivotTable, key)], key)
  }

  function IBufferLeaf(node: PNode) : Buffer
  requires P.WFNode(node);
  {
    imap key :: M.Merge(
      P.BucketLookup(node.buckets[P.Route(node.pivotTable, key)], key),
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
  requires P.WFPivotTable(node.pivotTable)
  {
    iset key | P.Route(node.pivotTable, key) == slotIndex
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

  function leftKeys(fusion: P.NodeFusion) : iset<Key>
  requires P.ValidFusion(fusion)
  {
    iset key |
      && Keyspace.lt(key, fusion.split_parent.pivotTable[fusion.slot_idx])
      && (fusion.slot_idx == 0 || Keyspace.lte(fusion.split_parent.pivotTable[fusion.slot_idx - 1], key))
  }

  function rightKeys(fusion: P.NodeFusion) : iset<Key>
  requires P.ValidFusion(fusion)
  {
    iset key |
      && Keyspace.lte(fusion.split_parent.pivotTable[fusion.slot_idx], key)
      && (fusion.slot_idx == |fusion.split_parent.pivotTable| - 1 ||
          Keyspace.lt(key, fusion.split_parent.pivotTable[fusion.slot_idx + 1]))
  }

  function IFusion(fusion: P.NodeFusion) : B.NodeFusion
  requires P.ValidFusion(fusion)
  {
    B.NodeFusion(
      fusion.parentref,
      fusion.fused_childref,
      fusion.left_childref,
      fusion.right_childref,
      INode(fusion.fused_parent),
      INode(fusion.split_parent),
      INode(fusion.fused_child),
      INode(fusion.left_child),
      INode(fusion.right_child),
      leftKeys(fusion),
      rightKeys(fusion)
    )
  }

  function IStep(betreeStep: P.BetreeStep) : B.BetreeStep
  requires P.ValidBetreeStep(betreeStep)
  {
    match betreeStep {
      case BetreeQuery(q) => B.BetreeQuery(IQuery(q))
      case BetreeInsert(ins) => B.BetreeInsert(IInsertion(ins))
      case BetreeFlush(flush) => B.BetreeFlush(IFlush(flush))
      case BetreeGrow(growth) => B.BetreeGrow(IGrow(growth))
      //case BetreeSplit(fusion) => B.BetreeSplit(IFusion(fusion))
      //case BetreeMerge(fusion) => B.BetreeMerge(IFusion(fusion))
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
          assert key in IReadOps(lookup)[idx].node.children;
          //assert B.LookupFollowsChildRefAtLayer(key, IReadOps(lookup), idx);
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

  lemma RouteIs(pivots: PivotTable, key: Key, idx: int)
  requires P.WFPivotTable(pivots)
  requires 0 <= idx <= |pivots|
  requires idx > 0 ==> Keyspace.lte(pivots[idx-1], key);
  requires idx < |pivots| ==> Keyspace.lt(key, pivots[idx]);
  ensures P.Route(pivots, key) == idx;
  {
  }

  lemma RefinesValidFusion(fusion: P.NodeFusion)
  requires P.ValidFusion(fusion)
  ensures B.ValidFusion(IFusion(fusion))
  {
    forall key | key in IFusion(fusion).left_keys
    ensures IMapsTo(IFusion(fusion).fused_parent.children, key, IFusion(fusion).fused_childref)
    {
      //assert Keyspace.lt(key, fusion.split_parent.pivotTable[fusion.slot_idx]);
      //assert (fusion.slot_idx == 0 || Keyspace.lte(fusion.split_parent.pivotTable[fusion.slot_idx - 1], key));

      /*
      if (fusion.slot_idx > 0) {
        assert fusion.split_parent.pivotTable[fusion.slot_idx - 1]
            == fusion.fused_parent.pivotTable[fusion.slot_idx - 1];
      }
      */
      if (fusion.slot_idx < |fusion.fused_parent.pivotTable|) {
        //assert fusion.fused_parent.pivotTable[fusion.slot_idx] == fusion.split_parent.pivotTable[fusion.slot_idx + 1];
        Keyspace.IsStrictlySortedImpliesLt(fusion.split_parent.pivotTable, fusion.slot_idx, fusion.slot_idx + 1);
        /*
        assert Keyspace.lt(
                fusion.split_parent.pivotTable[fusion.slot_idx],
                fusion.split_parent.pivotTable[fusion.slot_idx + 1]);
        assert Keyspace.lt(
                fusion.split_parent.pivotTable[fusion.slot_idx],
                fusion.fused_parent.pivotTable[fusion.slot_idx]);
        */
      }

      /*
      assert fusion.slot_idx > 0 ==> Keyspace.lte(fusion.fused_parent.pivotTable[fusion.slot_idx-1], key);
      assert fusion.slot_idx < |fusion.fused_parent.pivotTable| ==> Keyspace.lt(key, fusion.fused_parent.pivotTable[fusion.slot_idx]);
      */

      RouteIs(fusion.fused_parent.pivotTable, key, fusion.slot_idx);
      /*
      assert P.Route(fusion.fused_parent.pivotTable, key) == fusion.slot_idx;
      assert fusion.fused_parent.children.value[fusion.slot_idx] == fusion.fused_childref;
      assert fusion.fused_parent.children.value[P.Route(fusion.fused_parent.pivotTable, key)] == fusion.fused_childref;
      assert IMapsTo(IChildren(fusion.fused_parent), key, fusion.fused_childref);
      */
    }

    forall key | key in IFusion(fusion).right_keys
    ensures IMapsTo(IFusion(fusion).fused_parent.children, key, IFusion(fusion).fused_childref)
    {
      if (fusion.slot_idx > 0) {
        Keyspace.IsStrictlySortedImpliesLt(fusion.split_parent.pivotTable, fusion.slot_idx - 1, fusion.slot_idx);
      }
      RouteIs(fusion.fused_parent.pivotTable, key, fusion.slot_idx);
    }

    /*
    forall key | (key !in IFusion(fusion).left_keys) && (key !in IFusion(fusion).right_keys)
    ensures IMapsAgreeOnKey(IFusion(fusion).split_parent.children, IFusion(fusion).fused_parent.children, key)
    {
      var r := P.Route(fusion.fused_parent.pivotTable, key);
      if (r < fusion.slot_idx) {
        //assert fusion.split_parent.children.Some?;
        RouteIs(fusion.split_parent.pivotTable, key, r);
        /*
        assert r == P.Route(fusion.split_parent.pivotTable, key);
        assert IChildren(fusion.split_parent)[key] == fusion.split_parent.children.value[r];
        assert IChildren(fusion.split_parent)[key] == fusion.split_parent.children.value[r];
        assert IChildren(fusion.fused_parent)[key] == fusion.fused_parent.children.value[r];
        assert fusion.split_parent.children.value[r] == fusion.fused_parent.children.value[r];
        */

        assert IMapsAgreeOnKey(IFusion(fusion).split_parent.children, IFusion(fusion).fused_parent.children, key);
      } else if (r == fusion.slot_idx) {
        var pivot := fusion.split_parent.pivotTable[fusion.slot_idx];
        if (Keyspace.lte(pivot, key)) {
          if (fusion.slot_idx + 1 < |fusion.split_parent.pivotTable|) {
            assert fusion.split_parent.pivotTable[r + 1] == fusion.fused_parent.pivotTable[r];
            //assert Keyspace.lt(key, fusion.split_parent.pivotTable[r + 1]);
            //assert Keyspace.lt(key, fusion.split_parent.pivotTable[fusion.slot_idx + 1]);
          }
          assert key in IFusion(fusion).right_keys;
        } else {
          //assert Keyspace.lt(key, pivot);
          assert key in IFusion(fusion).left_keys;
        }
      } else {
        assert fusion.fused_parent.pivotTable[r-1] == fusion.split_parent.pivotTable[r];
        //assert Keyspace.lte(fusion.fused_parent.pivotTable[r-1], key);
        //assert Keyspace.lte(fusion.split_parent.pivotTable[r], key);

        if (r+1 < |fusion.split_parent.pivotTable|) {
          assert fusion.fused_parent.pivotTable[r] == fusion.split_parent.pivotTable[r + 1];
          //assert Keyspace.lt(key, fusion.fused_parent.pivotTable[r]);
          //assert Keyspace.lt(key, fusion.split_parent.pivotTable[r + 1]);
        }

        RouteIs(fusion.split_parent.pivotTable, key, r + 1);
        assert IMapsAgreeOnKey(IFusion(fusion).split_parent.children, IFusion(fusion).fused_parent.children, key);
      }
    }
    */

    forall key
    ensures P.BucketLookup(fusion.split_parent.buckets[P.Route(fusion.split_parent.pivotTable, key)], key)
         == P.BucketLookup(fusion.fused_parent.buckets[P.Route(fusion.fused_parent.pivotTable, key)], key)
    ensures (key !in IFusion(fusion).left_keys) && (key !in IFusion(fusion).right_keys) ==> IMapsAgreeOnKey(IFusion(fusion).split_parent.children, IFusion(fusion).fused_parent.children, key)
    {
      var r := P.Route(fusion.fused_parent.pivotTable, key);
      if (r < fusion.slot_idx) {
        RouteIs(fusion.split_parent.pivotTable, key, r);
      } else if (r == fusion.slot_idx) {
        var pivot := fusion.split_parent.pivotTable[fusion.slot_idx];
        if (Keyspace.lte(pivot, key)) {
          if (fusion.slot_idx + 1 < |fusion.split_parent.pivotTable|) {
            assert fusion.split_parent.pivotTable[r + 1] == fusion.fused_parent.pivotTable[r];
          }
          assert key in IFusion(fusion).right_keys;
        } else {
          assert key in IFusion(fusion).left_keys;
        }
      } else {
        assert fusion.fused_parent.pivotTable[r-1] == fusion.split_parent.pivotTable[r];

        if (r+1 < |fusion.split_parent.pivotTable|) {
          assert fusion.fused_parent.pivotTable[r] == fusion.split_parent.pivotTable[r + 1];
        }

        RouteIs(fusion.split_parent.pivotTable, key, r + 1);
      }
    }

    var child := fusion.fused_child;
    var left := fusion.left_child;
    var right := fusion.right_child;

    forall key | key in IFusion(fusion).left_keys
    ensures IMapsAgreeOnKey(IFusion(fusion).fused_child.children, IFusion(fusion).left_child.children, key)
    ensures IMapsAgreeOnKey(IFusion(fusion).fused_child.buffer, IFusion(fusion).left_child.buffer, key)
    {
      var r := P.Route(left.pivotTable, key);
      RouteIs(child.pivotTable, key, r);
    }

    forall key | key in IFusion(fusion).right_keys
    ensures IMapsAgreeOnKey(IFusion(fusion).fused_child.children, IFusion(fusion).right_child.children, key)
    ensures IMapsAgreeOnKey(IFusion(fusion).fused_child.buffer, IFusion(fusion).right_child.buffer, key)
    {
      var r := P.Route(right.pivotTable, key);
      if (r > 0) {
        assert right.pivotTable[r-1] == child.pivotTable[r + |left.buckets| - 1];
      }
      if (r < |right.pivotTable|) {
        assert right.pivotTable[r] == child.pivotTable[r + |left.buckets|];
      }
      RouteIs(child.pivotTable, key, r + |left.buckets|);
    }
  }

  lemma GetKeyInBucket(pivotTable: PivotTable, idx: int, anyKey: Key) returns (key: Key)
  requires P.WFPivotTable(pivotTable)
  requires 0 <= idx < P.PivotTableSize(pivotTable)
  ensures P.Route(pivotTable, key) == idx
  {
    if (idx == 0) {
      if (|pivotTable| > 0) {
        var key := Keyspace.SmallerElement(pivotTable[0]);
        RouteIs(pivotTable, key, 0);
        return key;
      } else {
        RouteIs(pivotTable, anyKey, 0);
        return anyKey;
      }
    } else {
      if (idx < |pivotTable|) {
        Keyspace.IsStrictlySortedImpliesLt(pivotTable, idx-1, idx);
      }
      RouteIs(pivotTable, pivotTable[idx-1], idx);
      return pivotTable[idx-1];
    }
  }

  lemma RefinesValidSplit(fusion: P.NodeFusion)
  requires P.ValidSplit(fusion)
  ensures P.ValidFusion(fusion)
  ensures B.ValidSplit(IFusion(fusion))
  {
    assert P.ValidFusion(fusion); // TODO

    forall ref | ref in IChildren(fusion.left_child).Values
    ensures ref in IChildren(fusion.fused_child).Values
    {
      var key :| IChildren(fusion.left_child)[key] == ref;
      var i := P.Route(fusion.left_child.pivotTable, key);
      //assert fusion.left_child.children.value[i] == ref;
      //assert fusion.fused_child.children.value[i] == ref;
      var key1 := GetKeyInBucket(fusion.fused_child.pivotTable, i, key);
      assert IChildren(fusion.fused_child)[key1] == ref;
    }
    forall ref | ref in IChildren(fusion.right_child).Values
    ensures ref in IChildren(fusion.fused_child).Values
    {
      var key :| IChildren(fusion.right_child)[key] == ref;
      var i := P.Route(fusion.right_child.pivotTable, key);
      var j := i + |fusion.left_child.buckets|;
      var key1 := GetKeyInBucket(fusion.fused_child.pivotTable, j, key);
      assert IChildren(fusion.fused_child)[key1] == ref;
    }
    RefinesValidFusion(fusion);
  }

  lemma RefinesValidMerge(fusion: P.NodeFusion)
  requires P.ValidMerge(fusion)
  ensures B.ValidMerge(IFusion(fusion))
  {
    RefinesValidFusion(fusion);

    // TODO
  }

  lemma RefinesValidBetreeStep(betreeStep: P.BetreeStep)
  requires P.ValidBetreeStep(betreeStep)
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
            P.BucketLookup(oldroot.buckets[P.Route(oldroot.pivotTable, ins.key)], ins.key),
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
  requires P.WFPivotTable(pivotTable)
  requires 0 <= i <= |buckets|;
  ensures key !in parentBucket && P.Route(pivotTable, key) < i ==>
      P.BucketLookup(P.AddMessagesToBuckets(pivotTable, i, buckets, parentBucket)[P.Route(pivotTable, key)], key)
   == P.BucketLookup(buckets[P.Route(pivotTable, key)], key)
  ensures key in parentBucket && P.Route(pivotTable, key) < i ==>
      P.BucketLookup(P.AddMessagesToBuckets(pivotTable, i, buckets, parentBucket)[P.Route(pivotTable, key)], key)
   == M.Merge(parentBucket[key],
      P.BucketLookup(buckets[P.Route(pivotTable, key)], key))
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
        assert P.WFBucket(flush.parent, flush.slotIndex);
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
    ensures P.WFBucket(newparent, i)
    {
      assert P.WFBucket(flush.parent, i);
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

  lemma {:fuel IOps,3} RefinesOps(betreeStep: P.BetreeStep)
  requires P.ValidBetreeStep(betreeStep)
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
        assert forall i | 0 <= i < |P.BetreeStepOps(betreeStep)| ::
            P.WFNode(P.BetreeStepOps(betreeStep)[i].node);
        assert IOps(P.BetreeStepOps(betreeStep)) == B.BetreeStepOps(IStep(betreeStep));
      }
      case BetreeMerge(fusion) => {
        assert forall i | 0 <= i < |P.BetreeStepOps(betreeStep)| ::
            P.WFNode(P.BetreeStepOps(betreeStep)[i].node);
        assert IOps(P.BetreeStepOps(betreeStep)) == B.BetreeStepOps(IStep(betreeStep));
      }
    }
  }
}
