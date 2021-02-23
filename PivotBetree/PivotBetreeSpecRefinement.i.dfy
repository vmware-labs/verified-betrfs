include "../Betree/BlockInterface.i.dfy"  
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "../MapSpec/MapSpec.s.dfy"
include "../Betree/Graph.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Message.i.dfy"
include "../Betree/BetreeSpec.i.dfy"
include "../Betree/Betree.i.dfy"
include "../Betree/BetreeInv.i.dfy"
include "PivotBetreeSpec.i.dfy"
include "PivotBetreeSpecWFNodes.i.dfy"
//
// Lays out the abstraction function between the datatypes, setting
// up for PivotBetree_Refines_Betree.
//

module PivotBetreeSpecRefinement {
  import B = BetreeSpec`Internal
  import P = PivotBetreeSpec`Internal
  import opened ValueMessage`Internal
  import MS = MapSpec
  import opened Maps
  import opened Sequences
  import opened Options
  import opened BoundedPivotsLib
  import opened BucketsLib
  import opened KeyType
  import PivotBetreeSpecWFNodes
  import opened BucketMaps
  import BucketFlushModel
  import Upperbounded_Lexicographic_Byte_Order

  type Node = B.G.Node
  type PNode = P.G.Node

  type Reference = B.G.Reference
  type Buffer = B.G.Buffer

  function IChildren(node: PNode) : (m: imap<Key, Reference>)
  requires (node.children.Some? ==> |node.buckets| == |node.children.value|)
  requires WFPivots(node.pivotTable)
  requires NumBuckets(node.pivotTable) == |node.buckets|
  {
    if node.children.Some? then (
      imap key:Key | BoundedKey(node.pivotTable, key) :: node.children.value[Route(node.pivotTable, key)]
    ) else (
      imap[]
    )
  }


  function BucketOptGet(bucket: BucketMap, key: Key) : Message
  {
    if key in bucket then bucket[key] else IdentityMessage()
  }

  function BucketOptListGet(blist: BucketList, pivots: PivotTable, key: Key) : Message
  requires WFBucketList(blist, pivots)
  requires BoundedKey(pivots, key)
  {
    BucketOptGet(blist[Route(pivots, key)].as_map(), key)
  }

  function IBufferInternal(node: PNode) : Buffer
  requires WFBucketList(node.buckets, node.pivotTable)
  {
    imap key:Key :: if BoundedKey(node.pivotTable, key) 
      then BucketOptListGet(node.buckets, node.pivotTable, key) else DefineDefault() 
    // safe because it's not reachable by any op
  }

  function IBufferLeaf(node: PNode) : Buffer
  requires WFBucketList(node.buckets, node.pivotTable)
  {
    imap key:Key :: if BoundedKey(node.pivotTable, key) then Merge(
      BucketOptListGet(node.buckets, node.pivotTable, key),
      DefineDefault()
    ) else DefineDefault()
  }

  function IBuffer(node: PNode) : Buffer
  requires WFBucketList(node.buckets, node.pivotTable)
  {
    if node.children.Some? then
      IBufferInternal(node)
    else
      IBufferLeaf(node)
  }

  // This is the main part of the story: the refinement from pivot node to betree node.
  function INode(node: PNode) : Node
  requires (node.children.Some? ==> |node.buckets| == |node.children.value|)
  requires WFBucketList(node.buckets, node.pivotTable)
  ensures B.WFNode(INode(node))
  {
    B.G.Node(IChildren(node), IBuffer(node))
  }


  predicate ReadOpsBucketsWellMarshalled(readOps: seq<P.Layer>)
  {
    forall i | 0 <= i < |readOps| ::
      forall j | 0 <= j < |readOps[i].node.buckets| ::
        BucketWellMarshalled(readOps[i].node.buckets[j])
  }

  function IReadOp(readOp: P.Layer) : (r: B.G.ReadOp)
  requires P.WFNode(readOp.node)
  ensures B.WFNode(r.node)
  {
    B.G.ReadOp(readOp.ref, INode(readOp.node))
  }

  function IReadOps(readOps: seq<P.Layer>) : seq<B.G.ReadOp>
  requires forall i | 0 <= i < |readOps| :: P.WFNode(readOps[i].node)
  ensures |readOps| == |IReadOps(readOps)|
  ensures forall i | 0 <= i < |IReadOps(readOps)| :: B.WFNode(IReadOps(readOps)[i].node)
  {
    if |readOps| == 0 then [] else
      IReadOps(readOps[..|readOps|-1]) + [IReadOp(readOps[|readOps|-1])]
  }

  function IQuery(q: P.LookupQuery) : B.LookupQuery
  requires P.ValidQuery(q)
  {
    B.LookupQuery(q.key, q.value, IReadOps(q.lookup))
  }

  function ISuccQuery(q: P.SuccQuery) : B.SuccQuery
  requires P.ValidSuccQuery(q)
  {
    B.SuccQuery(q.start, q.results, q.end, IReadOps(q.lookup))
  }

  function IInsertion(ins: P.MessageInsertion) : B.MessageInsertion
  requires P.ValidInsertion(ins)
  {
    B.MessageInsertion(ins.key, ins.msg, INode(ins.oldroot))
  }

  function MovedKeys(node: PNode, slotIndex: int) : iset<Key>
  requires WFPivots(node.pivotTable)
  {
    iset key | BoundedKey(node.pivotTable, key) && Route(node.pivotTable, key) == slotIndex
  }

  function FlushedKeys(flush: P.NodeFlush) : iset<Key>
  requires P.ValidFlush(flush)
  {
    //iset key | BoundedKey(node.pivotTable, key) && Route(node.pivotTable, key) == slotIndex && key in keys
    iset key | key in flush.parent.buckets[flush.slotIndex].as_map().Keys
            && key !in flush.newParentBucket.as_map().Keys
  }

  function IFlush(flush: P.NodeFlush) : B.NodeFlush
  requires P.ValidFlush(flush)
  {
    B.NodeFlush(flush.parentref, INode(flush.parent), flush.childref, INode(flush.child), flush.newchildref, MovedKeys(flush.parent, flush.slotIndex), FlushedKeys(flush))
  }

  function IGrow(growth: P.RootGrowth) : B.RootGrowth
  requires P.ValidGrow(growth)
  {
    B.RootGrowth(INode(growth.oldroot), growth.newchildref)
  }

  function ISplit(split: P.NodeFusion) : B.Redirect
  requires P.InvNode(split.fused_parent)
  requires P.InvNode(split.fused_child)
  requires P.ValidSplit(split)
  {
    PivotBetreeSpecWFNodes.ValidSplitWritesInvNodes(split);
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
  requires P.InvNode(split.split_parent)
  requires P.InvNode(split.left_child)
  requires P.InvNode(split.right_child)
  requires P.ValidMerge(split)
  {
    PivotBetreeSpecWFNodes.ValidMergeWritesInvNodes(split);
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
  requires forall i | 0 <= i < |P.BetreeStepReads(betreeStep)| :: P.InvNode(P.BetreeStepReads(betreeStep)[i].node)
  {
    match betreeStep {
      case BetreeQuery(q) => B.BetreeQuery(IQuery(q))
      case BetreeSuccQuery(sq) => B.BetreeSuccQuery(ISuccQuery(sq))
      case BetreeInsert(ins) => B.BetreeInsert(IInsertion(ins))
      case BetreeFlush(flush) => B.BetreeFlush(IFlush(flush))
      case BetreeGrow(growth) => B.BetreeGrow(IGrow(growth))
      case BetreeSplit(fusion) => (
        assert P.InvNode(P.BetreeStepReads(betreeStep)[0].node);
        assert P.InvNode(P.BetreeStepReads(betreeStep)[1].node);
        B.BetreeRedirect(ISplit(fusion))
      )
      case BetreeMerge(fusion) => (
        assert P.InvNode(P.BetreeStepReads(betreeStep)[0].node);
        assert P.InvNode(P.BetreeStepReads(betreeStep)[1].node);
        assert P.InvNode(P.BetreeStepReads(betreeStep)[2].node);
        B.BetreeRedirect(IMerge(fusion))
      )
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
  ensures P.LookupVisitsWellMarshalledBuckets(lookup, key) ==>
    B.InterpretLookup(IReadOps(lookup), key) == P.InterpretLookup(lookup, key)
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
      if P.LookupVisitsWellMarshalledBuckets(lookup, key) {
        assert B.InterpretLookup(IReadOps(lookup), key) == P.InterpretLookup(lookup, key);
      }
    }
  }

  lemma RefinesInterpretLookupAccountingForLeaf(lookup: P.Lookup, key: Key, value: Value)
  requires P.WFLookupForKey(lookup, key)
  ensures B.WFLookupForKey(IReadOps(lookup), key)
  ensures P.LookupVisitsWellMarshalledBuckets(lookup, key) ==>
      B.InterpretLookup(IReadOps(lookup), key) == P.InterpretLookupAccountingForLeaf(lookup, key)
  {
    RefinesLookup(lookup, key);

    if (Last(lookup).node.children.Some?) {
      RefinesInterpretLookup(lookup, key);
    } else {
      if |lookup| == 1 {
        if P.LookupVisitsWellMarshalledBuckets(lookup, key) {
          MergeIsAssociative(
              Update(NopDelta()),
              P.NodeLookup(lookup[0].node, key),
              DefineDefault());
          assert B.InterpretLookup(IReadOps(lookup), key)
              //== M.Merge(M.Update(M.NopDelta()), M.Merge(P.NodeLookup(lookup[0].node, key), M.DefineDefault()))
              //== M.Merge(M.Merge(M.Update(M.NopDelta()), P.NodeLookup(lookup[0].node, key)), DefineDefault())
              == Merge(P.InterpretLookup(lookup, key), DefineDefault())
              == P.InterpretLookupAccountingForLeaf(lookup, key);
        }
      } else {
        forall idx | P.ValidLayerIndex(DropLast(lookup), idx) && idx < |DropLast(lookup)| - 1
        ensures P.LookupFollowsChildRefAtLayer(key, DropLast(lookup), idx)
        {
          assert P.LookupFollowsChildRefAtLayer(key, lookup, idx);
        }

        assert P.LookupFollowsChildRefAtLayer(key, lookup, |lookup|-2);
        RefinesInterpretLookup(DropLast(lookup), key);

        if P.LookupVisitsWellMarshalledBuckets(lookup, key) {
          MergeIsAssociative(
              B.InterpretLookup(DropLast(IReadOps(lookup)), key),
              P.NodeLookup(Last(lookup).node, key),
              DefineDefault());
        }
            /*
        assert B.InterpretLookup(IReadOps(lookup), key)
            == Merge(B.InterpretLookup(DropLast(IReadOps(lookup)), key), Last(IReadOps(lookup)).node.buffer[key])
            == Merge(B.InterpretLookup(DropLast(IReadOps(lookup)), key), Merge(P.NodeLookup(Last(lookup).node, key), DefineDefault()))
            == Merge(Merge(B.InterpretLookup(DropLast(IReadOps(lookup)), key), P.NodeLookup(Last(lookup).node, key)), DefineDefault())
            == P.InterpretLookupAccountingForLeaf(lookup, key);
            */
      }
    }
  }

  lemma RefinesValidQuery(q: P.LookupQuery)
  requires P.ValidQuery(q)
  requires ReadOpsBucketsWellMarshalled(P.QueryReads(q))
  ensures B.ValidQuery(IQuery(q))
  {
    RefinesLookup(q.lookup, q.key);
    RefinesInterpretLookupAccountingForLeaf(q.lookup, q.key, q.value);
    assert P.LookupVisitsWellMarshalledBuckets(q.lookup, q.key);
  }

  lemma KeyWithinUpperBoundIsWithinLookup(
      lookup: P.Lookup, startKey: Key, key: Key, idx: int)
  requires P.LookupVisitsWFNodes(lookup)
  requires P.LookupBoundedKey(startKey, lookup)
  requires 0 <= idx < |lookup|
  requires var lookupUpperBound := P.LookupUpperBound(lookup, startKey);
    && (lookupUpperBound.Some? ==> P.G.Keyspace.lt(key, lookupUpperBound.value))
  ensures var r := Route(lookup[idx].node.pivotTable, startKey);
      && Keyspace.lt(KeyToElement(key), lookup[idx].node.pivotTable[r+1])
  {
    P.reveal_LookupUpperBound();
    if idx == |lookup| - 1 {
    } else {
      KeyWithinUpperBoundIsWithinLookup(DropLast(lookup), startKey, key, idx);
    }
  }

  lemma InUpperBoundAndNot(a: Key, end: MS.UI.RangeEnd, b: Key)
  requires MS.UpperBound(a, end)
  requires !MS.UpperBound(b, end)
  ensures P.G.Keyspace.lt(a, b)
  {
    match end {
      case EInclusive(key) => {
        assert P.G.Keyspace.lte(a, key);
        assert P.G.Keyspace.lt(key, b);
      }
      case EExclusive(key) => {
        assert P.G.Keyspace.lt(a, key);
        assert P.G.Keyspace.lte(key, b);
      }
      case PositiveInf => { }
    }
  }

  lemma InRangeImpliesSameRoute(start: MS.UI.RangeStart, key: Key, end: MS.UI.RangeEnd, lookup: P.Lookup, idx: int)
  requires MS.InRange(start, key, end)
  requires P.LookupVisitsWFNodes(lookup)
  requires
    var startKey := if start.NegativeInf? then [] else start.key;
    && P.LookupBoundedKey(startKey, lookup)
  requires
    var startKey := if start.NegativeInf? then [] else start.key;
    var lookupUpperBound := P.LookupUpperBound(lookup, startKey);
    && P.WFLookupForKey(lookup, startKey)
    && (lookupUpperBound.Some? ==> !MS.UpperBound(lookupUpperBound.value, end))
  requires 0 <= idx < |lookup|
  ensures BoundedKey(lookup[idx].node.pivotTable, key)
  ensures var startKey := if start.NegativeInf? then [] else start.key;
        Route(lookup[idx].node.pivotTable, startKey)
     == Route(lookup[idx].node.pivotTable, key) // don't know about bounded key
  {
    var startKey := if start.NegativeInf? then [] else start.key;

    var r := Route(lookup[idx].node.pivotTable, startKey);
    //assert r > 0 ==> Keyspace.lte(lookup[idx].node.pivotTable[r-1], startKey);

    P.G.Keyspace.EmptyLte(key);
    //assert Keyspace.lte([], key);
    //assert Keyspace.lte(startKey, key);

    assert MS.InRange(start, key, end);
    var lookupUpperBound := P.LookupUpperBound(lookup, startKey);
    //assert lookupUpperBound.Some? ==> !MS.UpperBound(lookupUpperBound.value, end);
    //assert MS.UpperBound(key, end);
    if (lookupUpperBound.Some?) {
      InUpperBoundAndNot(key, end, lookupUpperBound.value);
    }
    //assert lookupUpperBound.Some? ==> Keyspace.lt(key, lookupUpperBound.value);
    KeyWithinUpperBoundIsWithinLookup(lookup, startKey, key, idx);
    //assert r < |lookup[idx].node.pivotTable| ==> Keyspace.lt(q.key, lookup[idx].node.pivotTable[r]);
    RouteIs(lookup[idx].node.pivotTable, key, r);
  }

  lemma InRangeImpliesValidLookup(start: MS.UI.RangeStart, key: Key, end: MS.UI.RangeEnd, lookup: P.Lookup)
  requires MS.InRange(start, key, end)
  requires P.LookupVisitsWFNodes(lookup)
  requires
    var startKey := if start.NegativeInf? then [] else start.key;
    && P.LookupBoundedKey(startKey, lookup)
  requires
    var startKey := if start.NegativeInf? then [] else start.key;
    var lookupUpperBound := P.LookupUpperBound(lookup, startKey);
    && P.WFLookupForKey(lookup, startKey)
    && (lookupUpperBound.Some? ==> !MS.UpperBound(lookupUpperBound.value, end))
  ensures P.WFLookupForKey(lookup, key)
  {
    var startKey := if start.NegativeInf? then [] else start.key;

    forall idx | P.ValidLayerIndex(lookup, idx) && idx < |lookup| - 1 
    ensures P.LookupFollowsChildRefAtLayer(key, lookup, idx)
    ensures BoundedKey(lookup[idx].node.pivotTable, key)
    {
      assert P.LookupFollowsChildRefAtLayer(startKey, lookup, idx);
      InRangeImpliesSameRoute(start, key, end, lookup, idx);
    }
    InRangeImpliesSameRoute(start, key, end, lookup, |lookup|-1);
  }
 
  function InterpretBucketStack(buckets: seq<Bucket>, key: Key) : Message
  requires forall i | 0 <= i < |buckets| :: PreWFBucket(buckets[i])
  {
    if |buckets| == 0 then
      Update(NopDelta())
    else
      Merge(InterpretBucketStack(DropLast(buckets), key), BucketGet(Last(buckets).as_map(), key))
  }

  lemma BucketGetComposeSeq(buckets: seq<Bucket>, key: Key)
  requires forall i | 0 <= i < |buckets| :: PreWFBucket(buckets[i])
  ensures BucketGet(ComposeSeq(MapsOfBucketList(buckets)), key) == InterpretBucketStack(buckets, key);
  {
    reveal_ComposeSeq();
    reveal_Compose();
    if |buckets| == 0 {
    } else {
      calc {
        BucketGet(ComposeSeq(MapsOfBucketList(buckets)), key);
        Merge(BucketGet(ComposeSeq(DropLast(MapsOfBucketList(buckets))), key), BucketGet(Last(MapsOfBucketList(buckets)), key));
        {
          assert DropLast(MapsOfBucketList(buckets)) == MapsOfBucketList(DropLast(buckets));
          assert Last(MapsOfBucketList(buckets)) == Last(buckets).as_map();
        }
        Merge(BucketGet(ComposeSeq(MapsOfBucketList(DropLast(buckets))), key), BucketGet(Last(buckets).as_map(), key));
        {
          BucketGetComposeSeq(DropLast(buckets), key);
        }
        Merge(InterpretBucketStack(DropLast(buckets), key), BucketGet(Last(buckets).as_map(), key));
        InterpretBucketStack(buckets, key);
      }
    }
  }

  lemma InterpretBucketStackEqInterpretLookupIter(
      start: MS.UI.RangeStart, end: MS.UI.RangeEnd, startKey: Key,
      buckets: seq<Bucket>, lookup: P.Lookup, key: Key,
      j: int)
  requires startKey == if start.NegativeInf? then [] else start.key;
  requires P.LookupVisitsWFNodes(lookup)
  requires P.LookupBoundedKey(startKey, lookup)
  requires |lookup| == |buckets|
  requires (forall i | 0 <= i < |lookup| :: buckets[i] == lookup[i].node.buckets[Route(lookup[i].node.pivotTable, startKey)])
  requires MS.InRange(start, key, end)
  requires
    var lookupUpperBound := P.LookupUpperBound(lookup, startKey);
    && P.WFLookupForKey(lookup, startKey)
    && (lookupUpperBound.Some? ==> !MS.UpperBound(lookupUpperBound.value, end))
  requires 0 <= j <= |lookup|
  requires P.LookupBoundedKey(key, lookup)
  requires P.LookupVisitsWellMarshalledBuckets(lookup, key)
  requires BucketListWellMarshalled(buckets)
  ensures InterpretBucketStack(buckets[..j], key)
       == P.InterpretLookup(lookup[..j], key)
  {
    if j == 0 {
    } else {
      InRangeImpliesSameRoute(start, key, end, lookup, j-1);
      //var layer := lookup[j-1]
      //assert Route(layer.node.pivotTable, key) == Route(layer.node.pivotTable, startKey);

      InterpretBucketStackEqInterpretLookupIter(start, end, startKey,
          buckets, lookup, key, j-1);
      assert DropLast(buckets[..j]) == buckets[..j-1];
      assert DropLast(lookup[..j]) == lookup[..j-1];
    }
  }

  lemma InterpretBucketStackEqInterpretLookup(
      start: MS.UI.RangeStart, end: MS.UI.RangeEnd, startKey: Key,
      buckets: seq<Bucket>, lookup: P.Lookup, key: Key)
  requires startKey == if start.NegativeInf? then [] else start.key;
  requires P.LookupVisitsWFNodes(lookup)
  requires P.LookupBoundedKey(startKey, lookup)
  requires |lookup| == |buckets|
  requires (forall i | 0 <= i < |lookup| :: buckets[i] == lookup[i].node.buckets[Route(lookup[i].node.pivotTable, startKey)])
  requires MS.InRange(start, key, end)
  requires
    var lookupUpperBound := P.LookupUpperBound(lookup, startKey);
    && P.WFLookupForKey(lookup, startKey)
    && (lookupUpperBound.Some? ==> !MS.UpperBound(lookupUpperBound.value, end))
  requires P.LookupBoundedKey(key, lookup)
  requires P.LookupVisitsWellMarshalledBuckets(lookup, key)
  requires BucketListWellMarshalled(buckets)
  ensures InterpretBucketStack(buckets, key)
       == P.InterpretLookup(lookup, key)
  {
    InterpretBucketStackEqInterpretLookupIter(start, end, startKey, buckets, lookup, key, |lookup|);
    assert buckets[..|buckets|] == buckets;
    assert lookup[..|buckets|] == lookup;
  }

  lemma SuccQueryProperties(results: seq<UI.SuccResult>, buckets: seq<Bucket>,
      start: UI.RangeStart, end: UI.RangeEnd)
  requires BucketListWellMarshalled(buckets)
  requires forall i | 0 <= i < |buckets| :: PreWFBucket(buckets[i])
  requires results ==
        SortedSeqOfKeyValueMap(
          KeyValueMapOfBucket(
            ClampRange(ComposeSeq(MapsOfBucketList(buckets)), start, end)))
  ensures (forall i | 0 <= i < |results| ::
      P.BufferDefinesValue(InterpretBucketStack(buckets, results[i].key), results[i].value))
  ensures (forall i | 0 <= i < |results| :: results[i].value != MS.EmptyValue())
  ensures (forall i | 0 <= i < |results| :: MS.InRange(start, results[i].key, end))
  ensures (forall i, j | 0 <= i < j < |results| :: P.G.Keyspace.lt(results[i].key, results[j].key))
  ensures (forall key | MS.InRange(start, key, end) ::
        (forall i | 0 <= i < |results| :: results[i].key != key) ==>
        P.BufferDefinesEmptyValue(InterpretBucketStack(buckets, key))
      )
  {
    forall i | 0 <= i < |results|
    ensures P.BufferDefinesValue(InterpretBucketStack(buckets, results[i].key), results[i].value)
    ensures results[i].value != MS.EmptyValue()
    ensures MS.InRange(start, results[i].key, end)
    {
      SortedSeqOfKeyValueMaps(KeyValueMapOfBucket(ClampRange(ComposeSeq(MapsOfBucketList(buckets)), start, end)), i);
      reveal_KeyValueMapOfBucket();
      reveal_ClampRange();

      //var m := ComposeSeq(buckets)[results[i].key];
      //assert Merge(m, M.DefineDefault()).value == results[i].value;
      BucketGetComposeSeq(buckets, results[i].key);
      //assert m == InterpretBucketStack(buckets, results[i].key);
    }

    SortedSeqOfKeyValueMapHasSortedKeys(KeyValueMapOfBucket(
            ClampRange(ComposeSeq(MapsOfBucketList(buckets)), start, end)));

    forall key | MS.InRange(start, key, end) &&
        (forall i | 0 <= i < |results| :: results[i].key != key)
    ensures
      P.BufferDefinesEmptyValue(InterpretBucketStack(buckets, key))
    {
      if !P.BufferDefinesEmptyValue(InterpretBucketStack(buckets, key)) {
        reveal_KeyValueMapOfBucket();
        reveal_ClampRange();

        BucketGetComposeSeq(buckets, key);
        //assert BucketGet(ComposeSeq(buckets), key) == InterpretBucketStack(buckets, key);
        //assert key in KeyValueMapOfBucket(ClampRange(ComposeSeq(buckets), start, end));
        SortedSeqOfKeyValueHasKey(KeyValueMapOfBucket(ClampRange(ComposeSeq(MapsOfBucketList(buckets)), start, end)), key);
      }
    }
  }

  lemma RefinesValidSuccQuery(sq: P.SuccQuery)
  requires P.ValidSuccQuery(sq)
  requires ReadOpsBucketsWellMarshalled(P.SuccQueryReads(sq))
  ensures B.ValidSuccQuery(ISuccQuery(sq))
  {
    var q := ISuccQuery(sq);
    var startKey := if sq.start.NegativeInf? then [] else sq.start.key;

    SuccQueryProperties(sq.results, sq.buckets, sq.start, sq.end);

    forall i | 0 <= i < |q.results|
    ensures B.LookupKeyValue(q.lookup, q.results[i].key, q.results[i].value)
    {
      InRangeImpliesValidLookup(sq.start, sq.results[i].key, sq.end, sq.lookup);

      RefinesLookup(sq.lookup, sq.results[i].key);
      RefinesInterpretLookupAccountingForLeaf(sq.lookup, sq.results[i].key, sq.results[i].value);

      InterpretBucketStackEqInterpretLookup(sq.start, sq.end, startKey, sq.buckets, sq.lookup, sq.results[i].key);
    }

    forall key | MS.InRange(q.start, key, q.end)
        && (forall i | 0 <= i < |q.results| :: q.results[i].key != key)
    ensures B.LookupKeyValue(q.lookup, key, MS.EmptyValue())
    {
      InRangeImpliesValidLookup(sq.start, key, sq.end, sq.lookup);

      RefinesLookup(sq.lookup, key);
      RefinesInterpretLookupAccountingForLeaf(sq.lookup, key, MS.EmptyValue());
      //assert P.BufferDefinesEmptyValue(P.InterpretLookup(sq.lookup, key));
      //assert P.InterpretLookupAccountingForLeaf(sq.lookup, key) == M.DefineDefault();

      //assert M.DefaultValue() == MS.EmptyValue();

      /*assert B.InterpretLookup(IReadOps(sq.lookup), key).value
          == P.InterpretLookupAccountingForLeaf(sq.lookup, key).value
          == MS.EmptyValue();*/

      InterpretBucketStackEqInterpretLookup(sq.start, sq.end, startKey, sq.buckets, sq.lookup, key);
    }
  }

  lemma RefinesValidInsertion(ins: P.MessageInsertion)
  requires P.ValidInsertion(ins)
  requires ReadOpsBucketsWellMarshalled(P.InsertionReads(ins))
  ensures B.ValidInsertion(IInsertion(ins))
  {
  }

  lemma RefinesValidFlush(flush: P.NodeFlush)
  requires P.ValidFlush(flush)
  requires forall i | 0 <= i < |P.FlushReads(flush)| :: P.InvNode(P.FlushReads(flush)[i].node)
  requires ReadOpsBucketsWellMarshalled(P.FlushReads(flush))
  ensures B.ValidFlush(IFlush(flush))
  {
    assert P.InvNode(P.FlushReads(flush)[0].node);
    assert P.InvNode(P.FlushReads(flush)[1].node);
    forall key | key in flush.parent.buckets[flush.slotIndex].as_map().Keys
    ensures BoundedKey(flush.parent.pivotTable, key)
    ensures Route(flush.parent.pivotTable, key) == flush.slotIndex
    {
      assert WFBucketAt(
        flush.parent.buckets[flush.slotIndex],
        flush.parent.pivotTable,
        flush.slotIndex);
      PivotBetreeSpecWFNodes.bucket_keys_in_seq(
          flush.parent.buckets[flush.slotIndex]);
    }
  }

  lemma RefinesValidGrow(growth: P.RootGrowth)
  requires P.ValidGrow(growth)
  requires ReadOpsBucketsWellMarshalled(P.GrowReads(growth))
  ensures B.ValidGrow(IGrow(growth))
  {
  }

  lemma CutoffNodeAndKeepLeftAgree(node: PNode, node': PNode, pivot: Key, key: Key)
  requires P.WFNode(node)
  requires P.WFNode(node')
  requires BucketListWellMarshalled(node.buckets)
  requires ValidLeftCutOffKey(node.pivotTable, pivot)
  requires BoundedKey(node.pivotTable, key) && P.G.Keyspace.lt(key, pivot)
  requires node' == P.CutoffNodeAndKeepLeft(node, pivot);
  ensures IBuffer(node)[key] == IBuffer(node')[key]
  ensures IMapsAgreeOnKey(IChildren(node), IChildren(node'), key)
  {
    reveal_SplitBucketLeft();
    P.reveal_CutoffNodeAndKeepLeft();
    var i := Route(node'.pivotTable, key);

    var cLeft := CutoffForLeft(node.pivotTable, pivot);
    assert node.pivotTable[i] == node'.pivotTable[i];
    assert Keyspace.lt(KeyToElement(key), node'.pivotTable[i+1]);
    assert Keyspace.lt(KeyToElement(key), node.pivotTable[i+1]);
    RouteIs(node.pivotTable, key, i);
    PivotBetreeSpecWFNodes.SplitMaps(node.buckets[cLeft], pivot);
    //assert MapsAgreeOnKey(node.buckets[i].as_map(), node'.buckets[i].as_map(), key);
  }

  lemma CutoffNodeAndKeepRightAgree(node: PNode, node': PNode, pivot: Key, key: Key)
  requires P.WFNode(node)
  requires P.WFNode(node')
  requires BucketListWellMarshalled(node.buckets)
  requires BoundedKey(node.pivotTable, pivot)
  requires BoundedKey(node.pivotTable, key) && P.G.Keyspace.lte(pivot, key)
  requires node' == P.CutoffNodeAndKeepRight(node, pivot);
  ensures IBuffer(node)[key] == IBuffer(node')[key]
  ensures IMapsAgreeOnKey(IChildren(node), IChildren(node'), key)
  {
    reveal_SplitBucketRight();
    P.reveal_CutoffNodeAndKeepRight();
    var i := Route(node'.pivotTable, key);
    RouteIs(node.pivotTable, key, i + |node.pivotTable| - |node'.pivotTable|);
    var cRight := CutoffForRight(node.pivotTable, pivot);
    PivotBetreeSpecWFNodes.SplitMaps(node.buckets[cRight], pivot);
  }

  lemma CutoffNodeAgree(node: PNode, node': PNode, l: Key, r: Option<Key>, key: Key)
  requires P.WFNode(node)
  requires P.WFNode(node')
  requires BucketListWellMarshalled(node.buckets)
  requires P.ValidSplitKey(node, l, r)
  requires node' == P.CutoffNode(node, l, r)
  requires P.G.Keyspace.lte(l, key)
  requires r.Some? ==> P.G.Keyspace.lt(key, r.value)
  ensures IBuffer(node)[key] == IBuffer(node')[key]
  ensures IMapsAgreeOnKey(IChildren(node), IChildren(node'), key)
  {
    P.reveal_CutoffNode();
    if (r.Some?) {
      var node1 := P.CutoffNodeAndKeepLeft(node, r.value);
      PivotBetreeSpecWFNodes.BucketListWellMarshalledCutoffNodeAndKeepLeft(node, r.value);
      CutoffNodeAndKeepLeftAgree(node, node1, r.value, key);
      CutoffNodeAndKeepRightAgree(node1, node', l, key);
    } else {
      CutoffNodeAndKeepRightAgree(node, node', l, key);
    }
  }

  lemma WriteFusedChildInTermsOfLeftAndRight(l: PNode, r: PNode, child: PNode, pivot: Key, num_children_left: int)
  requires P.WFNode(l)
  requires P.WFNode(r)
  requires P.WFNode(child)
  requires 1 <= num_children_left < |child.buckets|
  requires l == P.SplitChildLeft(child, num_children_left)
  requires r == P.SplitChildRight(child, num_children_left)
  requires child.pivotTable[num_children_left].e == pivot
  ensures child == P.G.Node(
      concat3(l.pivotTable[..|l.pivotTable|-1], KeyToElement(pivot), r.pivotTable[1..]),
      if l.children.Some? then Some(l.children.value + r.children.value) else None,
      l.buckets + r.buckets
    )
  {
    reveal_concat3();
    assert child.pivotTable == concat3(l.pivotTable[..|l.pivotTable|-1], KeyToElement(pivot), r.pivotTable[1..]);
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
  requires BoundedKey(l.pivotTable, key) && P.G.Keyspace.lt(key, pivot)
  requires l.children.Some? <==> r.children.Some?
  requires node == P.G.Node(
      concat3(l.pivotTable[..|l.pivotTable|-1], KeyToElement(pivot), r.pivotTable[1..]),
      if l.children.Some? then Some(l.children.value + r.children.value) else None,
      l.buckets + r.buckets
    )
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
  requires BoundedKey(r.pivotTable, key) && P.G.Keyspace.lte(pivot, key)
  requires l.children.Some? <==> r.children.Some?
  requires node == P.G.Node(
      concat3(l.pivotTable[..|l.pivotTable|-1], KeyToElement(pivot), r.pivotTable[1..]),
      if l.children.Some? then Some(l.children.value + r.children.value) else None,
      l.buckets + r.buckets
    )
  ensures IBuffer(r)[key] == IBuffer(node)[key]
  ensures IMapsAgreeOnKey(IChildren(r), IChildren(node), key)
  {
    var i := Route(r.pivotTable, key);
    if i > 0 {
      assert node.pivotTable[i+|l.buckets|] == r.pivotTable[i];
    }
    assert node.pivotTable[i+|l.buckets|+1] == r.pivotTable[i+1];
    RouteIs(node.pivotTable, key, i + |l.buckets|);
  }

  lemma ValidLeftChildHasGoodPivots(f: P.NodeFusion)
  requires P.ValidSplit(f)
  ensures Keyspace.lte(f.split_parent.pivotTable[f.slot_idx], f.left_child.pivotTable[0])
  ensures Keyspace.lte(Last(f.left_child.pivotTable), f.split_parent.pivotTable[f.slot_idx+1])
  {
  }

  lemma ValidRightChildHasGoodPivots(f: P.NodeFusion)
  requires P.ValidSplit(f)
  ensures Keyspace.lte(f.split_parent.pivotTable[f.slot_idx+1], f.right_child.pivotTable[0])
  ensures Keyspace.lte(Last(f.right_child.pivotTable), f.split_parent.pivotTable[f.slot_idx+2])
  {
  }

  lemma ValidMergeChildHasGoodPivots(f: P.NodeFusion)
  requires P.ValidMerge(f)
  ensures Keyspace.lte(f.fused_parent.pivotTable[f.slot_idx], f.fused_child.pivotTable[0])
  ensures Keyspace.lte(Last(f.fused_child.pivotTable), f.fused_parent.pivotTable[f.slot_idx+1])
  {
  }

  lemma SplitMergeBuffersChildrenEq(node: PNode, node': PNode, idx: int)
  requires P.WFNode(node)
  requires P.WFNode(node')
  requires BucketListWellMarshalled(node.buckets)
  requires |node'.buckets| == |node.buckets| + 1
  requires 0 <= idx < |node.buckets|
  requires forall i | 0 <= i < idx :: node.buckets[i] == node'.buckets[i]
  requires node'.buckets[idx] == SplitBucketLeft(node.buckets[idx], GetKey(node'.pivotTable, idx+1))
  requires node'.buckets[idx+1] == SplitBucketRight(node.buckets[idx], GetKey(node'.pivotTable, idx+1))
  requires forall i | idx + 2 <= i < |node'.buckets| :: node'.buckets[i] == node.buckets[i-1]
  requires forall i | 0 <= i <= idx :: node.pivotTable[i] == node'.pivotTable[i]
  requires forall i | idx+1 < i < |node'.pivotTable| :: node'.pivotTable[i] == node.pivotTable[i-1]
  requires node.children.Some?
  requires node'.children.Some?
  requires forall i | 0 <= i < idx :: node.children.value[i] == node'.children.value[i]
  requires forall i | idx + 2 <= i < |node'.buckets| :: node'.children.value[i] == node.children.value[i-1]
  requires forall key :: BoundedKey(node.pivotTable, key) <==> BoundedKey(node'.pivotTable, key) // TODO: revisit
  ensures IBuffer(node) == IBuffer(node')
  ensures forall key:Key | key !in PivotTableBucketKeySet(node.pivotTable, idx) && BoundedKey(node.pivotTable, key) ::
      IChildren(node)[key] == IChildren(node')[key]
  {
    reveal_SplitBucketLeft();
    reveal_SplitBucketRight();

    forall key:Key | BoundedKey(node.pivotTable, key)
    ensures IBuffer(node)[key] == IBuffer(node')[key]
    ensures key !in PivotTableBucketKeySet(node.pivotTable, idx) ==> IChildren(node)[key] == IChildren(node')[key]
    {
      var i := Route(node'.pivotTable, key);
      if (i < idx) {
        RouteIs(node.pivotTable, key, i);
        assert node'.buckets[i] == node.buckets[i];
        assert IBuffer(node)[key] == IBuffer(node')[key];
        assert IChildren(node)[key] == IChildren(node')[key];
      } else if (i == idx || i == idx+1) {
        assert node'.pivotTable[idx+2] == node.pivotTable[idx+1];
        RouteIs(node.pivotTable, key, idx);
        assert IBuffer(node)[key] == IBuffer(node')[key] by {
          PivotBetreeSpecWFNodes.SplitMaps(node.buckets[idx], GetKey(node'.pivotTable, idx+1));
        }
        assert key in PivotTableBucketKeySet(node.pivotTable, idx);
      } else {
        assert node.pivotTable[i-1] == node'.pivotTable[i];
        assert node.pivotTable[i] == node'.pivotTable[i+1];
        RouteIs(node.pivotTable, key, i-1);
        assert node'.buckets[i] == node.buckets[i-1];
        assert IBuffer(node)[key] == IBuffer(node')[key];
        assert IChildren(node)[key] == IChildren(node')[key];
      }
    }
  }

  lemma MergeRouteNewChild(f: P.NodeFusion, r: B.Redirect, childref: Reference, ref: Reference) returns (key: Key)
  requires P.ValidMerge(f)
  requires P.InvNode(f.split_parent)
  requires P.InvNode(f.left_child)
  requires P.InvNode(f.right_child)
  requires r == IMerge(f)
  requires childref in r.new_children
  requires ref in r.new_children[childref].children.Values
  ensures IMapsTo(r.new_parent.children, key, childref)
        && IMapsTo(r.new_children[childref].children, key, ref)
        && key in r.keys
        && key in r.old_parent.children
  {
    PivotBetreeSpecWFNodes.ValidMergeWritesInvNodes(f);
    assert childref == f.fused_childref;
    var new_child := r.new_children[childref];
    var k :| k in new_child.children && new_child.children[k] == ref;
    var i := Route(f.fused_child.pivotTable, k);
    
    ValidMergeChildHasGoodPivots(f);
    key := GetKeyInChildBucket(f.fused_parent.pivotTable, f.fused_child.pivotTable, f.slot_idx, i);
  }

  lemma MergeChildrenConsistent(f: P.NodeFusion, r: B.Redirect, key: Key)
  requires P.ValidMerge(f)
  requires P.InvNode(f.split_parent)
  requires P.InvNode(f.left_child)
  requires P.InvNode(f.right_child)
  requires P.InvNode(f.fused_parent);
  requires P.InvNode(f.fused_child);
  requires r == IMerge(f)
  requires key in r.keys * r.old_parent.children.Keys
  ensures r.old_parent.children[key] in r.old_children
  ensures IMapsAgreeOnKey(
      r.new_children[r.new_parent.children[key]].buffer,
      r.old_children[r.old_parent.children[key]].buffer, key)
  ensures IMapsAgreeOnKey(
      r.new_children[r.new_parent.children[key]].children,
      r.old_children[r.old_parent.children[key]].children, key)
  {
    var lb := P.getlbound(f.split_parent, f.slot_idx);
    var ub := P.getubound(f.split_parent, f.slot_idx+1);

    var left := P.CutoffNode(f.left_child, lb , Some(f.pivot));
    var right := P.CutoffNode(f.right_child, f.pivot, ub);

    if (P.G.Keyspace.lt(key, f.pivot)) {
      RouteIs(f.split_parent.pivotTable, key, f.slot_idx);
      assert r.old_parent.children[key] == f.left_childref;
      assert r.old_children[r.old_parent.children[key]] == INode(f.left_child);
      CutoffNodeAgree(f.left_child, left, lb, Some(f.pivot), key);
        MergedNodeAndLeftAgree(left, right, f.fused_child, f.pivot, key);
      } else {
        assert f.split_parent.pivotTable[f.slot_idx+2] == f.fused_parent.pivotTable[f.slot_idx+1];
        RouteIs(f.split_parent.pivotTable, key, f.slot_idx + 1);
        assert r.old_parent.children[key] == f.right_childref;
        assert r.old_children[r.old_parent.children[key]] == INode(f.right_child);
        CutoffNodeAgree(f.right_child, right, f.pivot, ub, key);
        MergedNodeAndRightAgree(left, right, f.fused_child, f.pivot, key);
      }
  }

  lemma RefinesValidMerge(f: P.NodeFusion)
  requires P.ValidMerge(f)
  requires ReadOpsBucketsWellMarshalled(P.MergeReads(f))
  requires P.InvNode(f.split_parent)
  requires P.InvNode(f.left_child)
  requires P.InvNode(f.right_child)
  ensures B.ValidRedirect(IMerge(f))
  {
    var r := IMerge(f);
    PivotBetreeSpecWFNodes.ValidMergeWritesInvNodes(f);

    assert P.WFNode(P.MergeOps(f)[0].node);
    assert P.WFNode(P.MergeOps(f)[1].node);

    assert P.MergeReads(f)[0].node == f.split_parent;
    assert BucketListWellMarshalled(f.split_parent.buckets);

    forall ref | ref in IMapRestrict(r.old_parent.children, r.keys).Values
    ensures ref in r.old_childrefs
    {
      var key: Key :| IMapsTo(IMapRestrict(r.old_parent.children, r.keys), key, ref);
      assert key in r.keys;
      if (P.G.Keyspace.lt(key, f.pivot)) {
        RouteIs(f.split_parent.pivotTable, key, f.slot_idx);
        assert ref == f.left_childref;
      } else {
        assert f.split_parent.pivotTable[f.slot_idx + 2] == f.fused_parent.pivotTable[f.slot_idx + 1];
        RouteIs(f.split_parent.pivotTable, key, f.slot_idx+1);
        assert ref == f.right_childref;
      }
    }

    forall ref | ref in r.old_childrefs
    ensures ref in IMapRestrict(r.old_parent.children, r.keys).Values
    {
      assert ref == f.left_childref || ref == f.right_childref;
      if (ref == f.left_childref) {
        var key := GetKeyInBucket(f.split_parent.pivotTable, f.slot_idx);
        RouteIs(f.fused_parent.pivotTable, key, f.slot_idx);
        assert key in r.keys;
        assert key in IMapRestrict(r.old_parent.children, r.keys);
        assert IMapRestrict(r.old_parent.children, r.keys)[key] == ref;
        assert ref in IMapRestrict(r.old_parent.children, r.keys).Values;
      } else {
        var key := GetKeyInBucket(f.split_parent.pivotTable, f.slot_idx + 1);
        RouteIs(f.fused_parent.pivotTable, key, f.slot_idx);
        assert key in r.keys;
        assert key in IMapRestrict(r.old_parent.children, r.keys);
        assert IMapRestrict(r.old_parent.children, r.keys)[key] == ref;
        assert ref in IMapRestrict(r.old_parent.children, r.keys).Values;
      }
    }

    reveal_MergeBucketsInList();
    SplitOfMergeBucketsInList(f.split_parent.buckets, f.slot_idx, f.split_parent.pivotTable);
    SplitMergeBuffersChildrenEq(f.fused_parent, f.split_parent, f.slot_idx);

    // assert redirect.old_children[f.left_childref] == INode(f.left_child);
    // assert redirect.old_children[f.right_childref] == INode(f.right_child);
    assert forall k | k in r.keys :: Keyspace.lt(KeyToElement(k), f.fused_parent.pivotTable[f.slot_idx+1]);

    forall key:Key | key in r.keys * r.old_parent.children.Keys
    ensures r.old_parent.children[key] in r.old_children
    ensures IMapsAgreeOnKey(r.new_children[r.new_parent.children[key]].buffer, r.old_children[r.old_parent.children[key]].buffer, key)
    ensures IMapsAgreeOnKey(r.new_children[r.new_parent.children[key]].children, r.old_children[r.old_parent.children[key]].children, key)
    { MergeChildrenConsistent(f, r, key); }

    forall childref, ref | childref in r.new_children && ref in r.new_children[childref].children.Values
    ensures exists key ::
          && IMapsTo(r.new_parent.children, key, childref)
          && IMapsTo(r.new_children[childref].children, key, ref)
          && key in r.keys
          && key in r.old_parent.children
    { var key := MergeRouteNewChild(f, r, childref, ref); }
  }

  lemma SplitChildrenConsistent(f: P.NodeFusion, r: B.Redirect, key: Key)
  requires P.ValidSplit(f)
  requires P.InvNode(f.split_parent)
  requires P.InvNode(f.left_child)
  requires P.InvNode(f.right_child)
  requires P.InvNode(f.fused_parent)
  requires P.InvNode(f.fused_child)
  requires r == ISplit(f)
  requires key in r.keys * r.old_parent.children.Keys
  ensures r.old_parent.children[key] in r.old_children
  ensures r.new_parent.children[key] in r.new_children
  ensures IMapsAgreeOnKey(
    r.new_children[r.new_parent.children[key]].buffer,
    r.old_children[r.old_parent.children[key]].buffer, key)
  ensures IMapsAgreeOnKey(
    r.new_children[r.new_parent.children[key]].children,
    r.old_children[r.old_parent.children[key]].children,
    key)
  {
    var lbound := P.getlbound(f.fused_parent, f.slot_idx);
    var ubound := P.getubound(f.fused_parent, f.slot_idx);
    var ch := P.CutoffNode(f.fused_child, lbound, ubound);
    CutoffNodeAgree(f.fused_child, ch, lbound, ubound, key);

    if (P.G.Keyspace.lt(key, f.pivot)) {
      RouteIs(f.split_parent.pivotTable, key, f.slot_idx);
      assert r.new_parent.children[key] == f.left_childref;
      assert r.new_children[r.new_parent.children[key]] == INode(f.left_child);
      WriteFusedChildInTermsOfLeftAndRight(f.left_child, f.right_child, ch, f.pivot, f.num_children_left);
      MergedNodeAndLeftAgree(f.left_child, f.right_child, ch, f.pivot, key);
    } else {
      if ubound.None? {
        P.reveal_CutoffNode();
        P.reveal_CutoffNodeAndKeepRight();
        assert BoundedKey(f.right_child.pivotTable, key);
      }
      assert f.split_parent.pivotTable[f.slot_idx+1] == KeyToElement(f.pivot);
      assert f.split_parent.pivotTable[f.slot_idx+2] == f.fused_parent.pivotTable[f.slot_idx+1];
      RouteIs(f.split_parent.pivotTable, key, f.slot_idx+1);
      assert r.new_parent.children[key] == f.right_childref;
      assert r.new_children[r.new_parent.children[key]] == INode(f.right_child);
      WriteFusedChildInTermsOfLeftAndRight(f.left_child, f.right_child, ch, f.pivot, f.num_children_left);
      MergedNodeAndRightAgree(f.left_child, f.right_child, ch, f.pivot, key);
    }
  }

  lemma SplitRouteNewChild(f: P.NodeFusion, r: B.Redirect, childref: Reference, ref: Reference) returns (key: Key)
  requires P.ValidSplit(f)
  requires P.InvNode(f.fused_parent)
  requires P.InvNode(f.fused_child)
  requires r == ISplit(f)
  requires childref in r.new_children
  requires ref in r.new_children[childref].children.Values
  ensures IMapsTo(r.new_parent.children, key, childref)
    && IMapsTo(r.new_children[childref].children, key, ref)
    && key in r.keys
    && key in r.old_parent.children
  {
    PivotBetreeSpecWFNodes.ValidSplitWritesInvNodes(f);
    var new_child := r.new_children[childref];
    var k :| k in new_child.children && new_child.children[k] == ref;

    var parent_slot;
    var lr_child;
    if (childref == f.left_childref) {
      parent_slot := f.slot_idx;
      lr_child := f.left_child;
    } else {
      parent_slot := f.slot_idx + 1;
      lr_child := f.right_child;
    }

    ValidLeftChildHasGoodPivots(f);
    ValidRightChildHasGoodPivots(f);

    var child_slot := Route(lr_child.pivotTable, k);
    key := GetKeyInChildBucket(f.split_parent.pivotTable, lr_child.pivotTable, parent_slot, child_slot);

    assert IMapsTo(r.new_parent.children, key, childref);
    assert IMapsTo(r.new_children[childref].children, key, ref);
    assert key in r.keys;
    assert key in r.old_parent.children;
  }

  lemma RefinesValidSplit(f: P.NodeFusion)
  requires P.ValidSplit(f)
  requires ReadOpsBucketsWellMarshalled(P.SplitReads(f))
  requires P.InvNode(f.fused_parent)
  requires P.InvNode(f.fused_child)
  ensures B.ValidRedirect(ISplit(f))
  {
    var r := ISplit(f);
    PivotBetreeSpecWFNodes.ValidSplitWritesInvNodes(f);

    assert P.SplitReads(f)[0].node == f.fused_parent;
    assert BucketListWellMarshalled(f.fused_parent.buckets);
    WellMarshalledSplitBucketInList(f.fused_parent.buckets, f.slot_idx,f.pivot);

    // assert (forall ref :: ref in IMapRestrict(r.old_parent.children, r.keys).Values ==> ref in r.old_childrefs);
    forall ref | ref in r.old_childrefs
    ensures ref in IMapRestrict(r.old_parent.children, r.keys).Values
    {
      assert ref == f.fused_childref;
      var key := GetKeyInBucket(f.fused_parent.pivotTable, f.slot_idx);
      assert IMapRestrict(r.old_parent.children, r.keys)[key] == ref;
    }

    reveal_SplitBucketInList();
    SplitMergeBuffersChildrenEq(f.fused_parent, f.split_parent, f.slot_idx);

    forall childref, ref | childref in r.new_children && ref in r.new_children[childref].children.Values
    ensures exists key ::
          && IMapsTo(r.new_parent.children, key, childref)
          && IMapsTo(r.new_children[childref].children, key, ref)
          && key in r.keys
          && key in r.old_parent.children
    { var key := SplitRouteNewChild(f, r, childref, ref); }

    forall key:Key | key in r.keys * r.old_parent.children.Keys
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
    { SplitChildrenConsistent(f, r, key); }

    assert (forall ref :: ref in IMapRestrict(r.new_parent.children, r.keys).Values ==> ref in r.new_childrefs);
    assert r.new_children.Keys == (iset ref | ref in r.new_childrefs);
  }

  lemma RefinesValidBetreeStep(betreeStep: P.BetreeStep)
  requires P.ValidBetreeStep(betreeStep)
  requires forall i | 0 <= i < |P.BetreeStepReads(betreeStep)| :: P.InvNode(P.BetreeStepReads(betreeStep)[i].node)
  requires !betreeStep.BetreeRepivot?
  requires ReadOpsBucketsWellMarshalled(P.BetreeStepReads(betreeStep))
  ensures B.ValidBetreeStep(IStep(betreeStep))
  {
    match betreeStep {
      case BetreeQuery(q) => RefinesValidQuery(q);
      case BetreeSuccQuery(sq) => RefinesValidSuccQuery(sq);
      case BetreeInsert(ins) => RefinesValidInsertion(ins);
      case BetreeFlush(flush) => RefinesValidFlush(flush);
      case BetreeGrow(growth) => RefinesValidGrow(growth);
      case BetreeSplit(fusion) => {
        assert P.InvNode(P.BetreeStepReads(betreeStep)[0].node);
        assert P.InvNode(P.BetreeStepReads(betreeStep)[1].node);
        RefinesValidSplit(fusion);
      }
      case BetreeMerge(fusion) => {
        assert P.InvNode(P.BetreeStepReads(betreeStep)[0].node);
        assert P.InvNode(P.BetreeStepReads(betreeStep)[1].node);
        assert P.InvNode(P.BetreeStepReads(betreeStep)[2].node);
        RefinesValidMerge(fusion);
      }
    }
  }

  lemma {:fuel IReadOps,3} RefinesReadOps(betreeStep: P.BetreeStep)
  requires P.ValidBetreeStep(betreeStep)
  requires forall i | 0 <= i < |P.BetreeStepReads(betreeStep)| :: P.InvNode(P.BetreeStepReads(betreeStep)[i].node)
  requires !betreeStep.BetreeRepivot?
  requires ReadOpsBucketsWellMarshalled(P.BetreeStepReads(betreeStep))
  ensures B.ValidBetreeStep(IStep(betreeStep))
  ensures IReadOps(P.BetreeStepReads(betreeStep)) == B.BetreeStepReads(IStep(betreeStep))
  {
    RefinesValidBetreeStep(betreeStep);
  }

  // interpret the pivot-y Ops (from our little cache DSL) to their Betree (non-pivot) versions.
  function IOp(op: P.G.Op) : B.G.Op
  requires P.InvNode(op.node)
  {
    match op {
      case AllocOp(ref, block) => B.G.AllocOp(ref, INode(block))
      case WriteOp(ref, block) => B.G.WriteOp(ref, INode(block))
    }
  }

  function IOps(ops: seq<P.G.Op>) : seq<B.G.Op>
  requires forall i | 0 <= i < |ops| :: P.InvNode(ops[i].node)
  {
    if |ops| == 0 then [] else
      IOps(ops[..|ops|-1]) + [IOp(ops[|ops|-1])]
  }

  lemma InsertRefinesOps(ins: P.MessageInsertion)
  requires P.ValidInsertion(ins)
  requires forall i | 0 <= i < |P.InsertionReads(ins)| :: P.InvNode(P.InsertionReads(ins)[i].node)
  requires B.ValidInsertion(IInsertion(ins))
  ensures forall i | 0 <= i < |P.InsertionOps(ins)| ::
      P.InvNode(P.InsertionOps(ins)[i].node)
  ensures IOps(P.InsertionOps(ins)) == B.InsertionOps(IInsertion(ins))
  {
    assert P.InvNode(P.InsertionReads(ins)[0].node);
    PivotBetreeSpecWFNodes.ValidInsertWritesInvNodes(ins);
    assert P.InvNode(P.InsertionOps(ins)[0].node);

    var newroot := P.AddMessageToNode(ins.oldroot, ins.key, ins.msg);
    var newroot' := B.AddMessageToNode(INode(ins.oldroot), ins.key, ins.msg);

    forall key:Key
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
          MergeIsAssociative(
            ins.msg,
            BucketGet(oldroot.buckets[Route(oldroot.pivotTable, ins.key)].as_map(), ins.key),
            DefineDefault()
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

  lemma AddMessagesToNodeResult(node: PNode, bucket: BucketMap, node': PNode, key: Key)
  requires P.InvNode(node)
  requires P.WFNode(node')
  requires WFBucketListProper(node'.buckets, node'.pivotTable);
  requires BucketListWellMarshalled(node.buckets)
  requires BoundedKey(node.pivotTable, key)
  requires BoundedKey(node'.pivotTable, key)
  requires node'.pivotTable == node.pivotTable
  requires node'.children == node.children
  requires MapsOfBucketList(node'.buckets)
      == BucketListFlush(bucket, MapsOfBucketList(node.buckets), node.pivotTable)
  ensures WFBucketListProper(node'.buckets, node'.pivotTable);
  ensures key !in bucket ==> P.NodeLookup(node', key) == P.NodeLookup(node, key)
  ensures key in bucket ==> P.NodeLookup(node', key) == Merge(bucket[key], P.NodeLookup(node, key))
  {
    //GetBucketListFlushEqMerge(bucket, node.buckets, node.pivotTable, key);
    var i := Route(node.pivotTable, key);
    assert node'.buckets[i].as_map() == 
        BucketListItemFlush(bucket, node.buckets[i].as_map(), node.pivotTable, i);
  }

  lemma {:fuel IOps,2} FlushRefinesOps(flush: P.NodeFlush)
  requires P.ValidFlush(flush)
  requires forall i | 0 <= i < |P.FlushReads(flush)| :: P.InvNode(P.FlushReads(flush)[i].node)
  requires B.ValidFlush(IFlush(flush))
  ensures forall i | 0 <= i < |P.FlushOps(flush)| ::
      P.InvNode(P.FlushOps(flush)[i].node)
  ensures IOps(P.FlushOps(flush)) == B.FlushOps(IFlush(flush))
  {
    assert P.InvNode(P.FlushReads(flush)[0].node);
    assert P.InvNode(P.FlushReads(flush)[1].node);
    PivotBetreeSpecWFNodes.ValidFlushWritesInvNodes(flush);

    var newparent := P.G.Node(
        flush.parent.pivotTable,
        Some(flush.parent.children.value[flush.slotIndex := flush.newchildref]),
        flush.parent.buckets[flush.slotIndex := flush.newParentBucket]
      );
    var pfr := BucketFlushModel.partialFlush(
          flush.parent.buckets[flush.slotIndex], flush.child.pivotTable, flush.child.buckets);
    var newchild := flush.child.(buckets := pfr.bots);
    var allocop := P.G.AllocOp(flush.newchildref, newchild);
    var writeop := P.G.WriteOp(flush.parentref, newparent);

    var flushedKeys := BucketFlushModel.partialFlushCorrect(
        flush.parent.buckets[flush.slotIndex], flush.child.pivotTable, flush.child.buckets);

    // equality of set and iset:
    forall k | k in flushedKeys ensures k in FlushedKeys(flush) {
      reveal_BucketComplement();
      //assert k in flush.parent.buckets[flush.slotIndex].as_map().Keys by {
      PivotBetreeSpecWFNodes.bucket_keys_equiv(flush.parent.buckets[flush.slotIndex]); //}
      //assert k !in flush.newParentBucket.as_map().Keys;
    }
    forall k | k in FlushedKeys(flush) ensures k in flushedKeys {
      reveal_BucketComplement();
    }

    var isec := BucketIntersect(flush.parent.buckets[flush.slotIndex].as_map(), flushedKeys);

    assert P.WFNode(newchild);
    assert P.WFNode(newparent);

    var flush' := IFlush(flush);
    var parentref := flush'.parentref;
    var parent := flush'.parent;
    var childref := flush'.childref;
    var child := flush'.child;
    var newchildref := flush'.newchildref;

    var newbuffer := imap k:Key :: (if k in flush'.flushedKeys then Merge(parent.buffer[k], child.buffer[k]) else child.buffer[k]);
    var newchild' := B.G.Node(child.children, newbuffer);
    var newparentbuffer := imap k:Key :: (if k in flush'.flushedKeys then Update(NopDelta()) else parent.buffer[k]);
    var newparentchildren := imap k:Key | k in parent.children :: (if k in flush'.movedKeys then newchildref else parent.children[k]);
    var newparent' := B.G.Node(newparentchildren, newparentbuffer);
    var allocop' := B.G.AllocOp(newchildref, newchild');
    var writeop' := B.G.WriteOp(parentref, newparent');

    reveal_BucketIntersect();
    reveal_BucketComplement();

    forall k: Key | BoundedKey(flush.child.pivotTable, k)
    ensures IBuffer(newchild)[k] == newbuffer[k]
    {
      AddMessagesToNodeResult(flush.child, isec, newchild, k);
      if (k in flush'.flushedKeys) {
        if (newchild.children.Some?) {
          assert IBuffer(newchild)[k] == newbuffer[k];
        } else {
          MergeIsAssociative(BucketGet(isec, k), P.NodeLookup(flush.child, k), DefineDefault());
          /*
          assert IBuffer(newchild)[k]
              == M.Merge(P.NodeLookup(newchild, k), M.DefineDefault())
              == M.Merge(M.Merge(BucketGet(isec, k), P.NodeLookup(flush.child, k)), M.DefineDefault())
              == Merge(BucketGet(isec, k), Merge(P.NodeLookup(flush.child, k), DefineDefault()))
              == newbuffer[k];*/
        }
      } else {
        //assert P.NodeHasWFBucketAt(flush.parent, flush.slotIndex);
        //assert k !in isec;
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

    /*forall i | 0 <= i < |newparent.buckets|
    ensures P.NodeHasWFBucketAt(newparent, i)
    {
      assert P.NodeHasWFBucketAt(flush.parent, i);
    }*/
    //assert P.WFNode(newparent);

    //assert IChildren(newchild) == newchild'.children;
    //assert IBuffer(newchild) == newbuffer;

    forall k: Key | BoundedKey(flush.parent.pivotTable, k)
    ensures IChildren(newparent)[k] == newparent'.children[k]
    {
      if (k in flush'.flushedKeys) {
        RouteIs(flush.parent.pivotTable, k, flush.slotIndex);
        assert IChildren(newparent)[k] == newparent'.children[k];
      } else if k in flush'.movedKeys {
        assert IChildren(newparent)[k] == newparent'.children[k];
      } else {
        // not in bound
        assert IChildren(newparent)[k] == newparent'.children[k];
      }
    }

    assert IChildren(newparent) == newparent'.children;
    assert IBuffer(newparent) == newparentbuffer;

    assert INode(newchild) == newchild';
    assert INode(newparent) == newparent';

    assert IOp(allocop) == allocop';
    assert IOp(writeop) == writeop';
  }

  lemma {:fuel IOps,3} GrowRefinesOps(growth: P.RootGrowth)
  requires P.ValidGrow(growth)
  requires forall i | 0 <= i < |P.GrowReads(growth)| :: P.InvNode(P.GrowReads(growth)[i].node)
  requires B.ValidGrow(IGrow(growth))
  ensures forall i | 0 <= i < |P.GrowOps(growth)| ::
      P.InvNode(P.GrowOps(growth)[i].node)
  ensures IOps(P.GrowOps(growth)) == B.GrowOps(IGrow(growth))
  {
    assert P.InvNode(P.GrowReads(growth)[0].node);
    PivotBetreeSpecWFNodes.ValidGrowWritesInvNodes(growth);

    var newroot := P.G.Node(InitPivotTable(), Some([growth.newchildref]), [BucketsLib.EmptyBucket()]);
    P.PivotsHasAllKeys(newroot.pivotTable);

    // observe: (I don't know really know why this is necessary)
    assert B.GrowOps(IGrow(growth))[1] 
        == B.G.WriteOp(B.G.Root(), INode(newroot));
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
  requires P.InvNode(f.fused_parent)
  requires P.InvNode(f.fused_child)
  requires B.ValidRedirect(ISplit(f))
  ensures forall i | 0 <= i < |P.SplitOps(f)| ::
      P.InvNode(P.SplitOps(f)[i].node)
  ensures IOps(P.SplitOps(f)) == B.RedirectOps(ISplit(f))
  {
    PivotBetreeSpecWFNodes.ValidSplitWritesInvNodes(f);
    assert IOp(P.G.AllocOp(f.left_childref, f.left_child)) == B.RedirectOps(ISplit(f))[0];
    assert IOp(P.G.AllocOp(f.right_childref, f.right_child)) == B.RedirectOps(ISplit(f))[1];
    assert IOp(P.G.WriteOp(f.parentref, f.split_parent)) == B.RedirectOps(ISplit(f))[2];

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
  requires P.InvNode(f.split_parent)
  requires P.InvNode(f.left_child)
  requires P.InvNode(f.right_child)
  requires B.ValidRedirect(IMerge(f))
  ensures forall i | 0 <= i < |P.MergeOps(f)| ::
      P.InvNode(P.MergeOps(f)[i].node)
  ensures IOps(P.MergeOps(f)) == B.RedirectOps(IMerge(f))
  {
    PivotBetreeSpecWFNodes.ValidMergeWritesInvNodes(f);
  }

  // The meaty lemma: If we mutate the nodes of a pivot-y cache according to a
  // (generic-DSL) BetreeStep, under the INode interpretation, the same
  // mutation happens to the imap-y cache.
  lemma {:fuel IOps,3} RefinesOps(betreeStep: P.BetreeStep)
  requires P.ValidBetreeStep(betreeStep)
  requires !betreeStep.BetreeRepivot?
  requires ReadOpsBucketsWellMarshalled(P.BetreeStepReads(betreeStep))
  requires forall i | 0 <= i < |P.BetreeStepReads(betreeStep)| :: P.InvNode(P.BetreeStepReads(betreeStep)[i].node)
  ensures B.ValidBetreeStep(IStep(betreeStep))
  ensures forall i | 0 <= i < |P.BetreeStepOps(betreeStep)| ::
      P.InvNode(P.BetreeStepOps(betreeStep)[i].node)
  ensures IOps(P.BetreeStepOps(betreeStep)) == B.BetreeStepOps(IStep(betreeStep))
  {
    RefinesValidBetreeStep(betreeStep);

    match betreeStep {
      case BetreeQuery(q) => {
        assert forall i | 0 <= i < |P.BetreeStepOps(betreeStep)| ::
            P.InvNode(P.BetreeStepOps(betreeStep)[i].node);
        assert IOps(P.BetreeStepOps(betreeStep)) == B.BetreeStepOps(IStep(betreeStep));
      }
      case BetreeSuccQuery(q) => {
        assert forall i | 0 <= i < |P.BetreeStepOps(betreeStep)| ::
            P.InvNode(P.BetreeStepOps(betreeStep)[i].node);
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
        assert P.InvNode(P.BetreeStepReads(betreeStep)[0].node);
        assert P.InvNode(P.BetreeStepReads(betreeStep)[1].node);
        SplitRefinesOps(fusion);
      }
      case BetreeMerge(fusion) => {
        assert P.InvNode(P.BetreeStepReads(betreeStep)[0].node);
        assert P.InvNode(P.BetreeStepReads(betreeStep)[1].node);
        assert P.InvNode(P.BetreeStepReads(betreeStep)[2].node);
        MergeRefinesOps(fusion);
      }
    }
  }

  /*lemma IBufferLeafEqJoin(node: PNode)
  requires P.InvNode(node)
  requires BucketListWellMarshalled(node.buckets)
  ensures IBufferLeaf(node) == imap key :: if BoundedKey(node.pivotTable, key) then Merge(BucketGet(JoinBucketList(node.buckets), key), DefineDefault()) else DefineDefault() 
  {
    forall key:Key | BoundedKey(node.pivotTable, key)
    ensures IBufferLeaf(node)[key] == Merge(BucketGet(JoinBucketList(node.buckets), key), DefineDefault())
    {
      forall i | 0 <= i < |node.buckets| ensures WFBucketAt(node.buckets[i], node.pivotTable, i)
      {
      }
      GetJoinBucketListEq(node.buckets, node.pivotTable, key);
    }
  }*/

  lemma RepivotPreservesNode(r: P.Repivot)
  requires P.ValidRepivot(r)
  requires forall i | 0 <= i < |P.RepivotReads(r)| :: P.InvNode(P.RepivotReads(r)[i].node)
  ensures P.InvNode(P.ApplyRepivot(r))
  ensures INode(r.leaf) == INode(P.ApplyRepivot(r))
  {
    assert P.InvNode(P.RepivotReads(r)[0].node);
    PivotBetreeSpecWFNodes.InvApplyRepivot(r);

    P.PivotsHasAllKeys(r.pivots);
    assert r.pivots[1] == KeyToElement(r.pivot);

    PivotBetreeSpecWFNodes.SplitMaps(r.leaf.buckets[0], r.pivot);

    /*var leaf'_buckets := [
          SplitBucketLeft(r.leaf.buckets[0], r.idx),
          SplitBucketRight(r.leaf.buckets[0], r.idx)
        ];*/

    //PivotBetreeSpecWFNodes.bucket_keys_equiv(r.leaf.buckets[0]);
    //PivotBetreeSpecWFNodes.bucket_keys_equiv(leaf'_buckets[0]);
    //PivotBetreeSpecWFNodes.bucket_keys_equiv(leaf'_buckets[1]);

    /*var buckets1 := r.leaf.buckets;
    P.PivotsHasAllKeys(r.pivots);
    BoundedBucketListJoin(buckets1, r.pivots);
    var joined := JoinBucketList(buckets1);
    WFJoinBucketList(buckets1);
    var buckets2 := SplitBucketOnPivots(joined, r.pivots);
    WFSplitBucketOnPivots(joined, r.pivots);

    forall i | 0 <= i < |buckets1|
    ensures forall key:Key | key in buckets1[i].as_map() :: buckets1[i].as_map()[key] != IdentityMessage()
    {
      //assert P.NodeHasWFBucketAt(r.leaf, i);
    }
    WFJoinBucketList(r.leaf.buckets);
    JoinBucketsSplitBucketOnPivotsCancel(joined, r.pivots);
    assert JoinBucketList(buckets1) == JoinBucketList(buckets2);
    
    IBufferLeafEqJoin(r.leaf);
    IBufferLeafEqJoin(P.ApplyRepivot(r));

    BoundedBucketListJoin(buckets1, r.leaf.pivotTable);
    assert BoundedBucket(joined, r.leaf.pivotTable);*/
  }
}
