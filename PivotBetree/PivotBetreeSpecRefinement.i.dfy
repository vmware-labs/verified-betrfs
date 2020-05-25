include "../Betree/BlockInterface.i.dfy"  
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Maps.s.dfy"
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
  import opened PivotsLib
  import opened BucketsLib
  import opened KeyType
  import PivotBetreeSpecWFNodes

  type Node = B.G.Node
  type PNode = P.G.Node

  type Reference = B.G.Reference
  type Buffer = B.G.Buffer

  function IChildren(node: PNode) : imap<Key, Reference>
  requires (node.children.Some? ==> |node.buckets| == |node.children.value|)
  requires WFPivots(node.pivotTable)
  requires NumBuckets(node.pivotTable) == |node.buckets|
  {
    if node.children.Some? then (
      imap key:Key :: node.children.value[Route(node.pivotTable, key)]
    ) else (
      imap[]
    )
  }

  function BucketOptGet(bucket: Bucket, key: Key) : Message
  {
    if key in bucket.b then bucket.b[key] else IdentityMessage()
  }

  function BucketOptListGet(blist: BucketList, pivots: PivotTable, key: Key) : Message
  requires WFBucketList(blist, pivots)
  {
    BucketOptGet(blist[Route(pivots, key)], key)
  }

  function IBufferInternal(node: PNode) : Buffer
  requires WFBucketList(node.buckets, node.pivotTable)
  {
    imap key:Key :: BucketOptListGet(node.buckets, node.pivotTable, key)
  }

  function IBufferLeaf(node: PNode) : Buffer
  requires WFBucketList(node.buckets, node.pivotTable)
  {
    imap key:Key :: Merge(
      BucketOptListGet(node.buckets, node.pivotTable, key),
      DefineDefault()
    )
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
  {
    B.G.Node(IChildren(node), IBuffer(node))
  }

//~  lemma WFNodeRefinesWFNode(node: PNode)
//~  requires P.WFNode(node)
//~  ensures B.WFNode(INode(node))
//~  {
//~  }

  predicate ReadOpsBucketsWellMarshalled(readOps: seq<P.G.ReadOp>)
  {
    forall i | 0 <= i < |readOps| ::
      forall j | 0 <= j < |readOps[i].node.buckets| ::
        BucketWellMarshalled(readOps[i].node.buckets[j])
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
    iset key | Route(node.pivotTable, key) == slotIndex
  }

  function FlushedKeys(node: PNode, slotIndex: int, keys: set<Key>) : iset<Key>
  requires WFPivots(node.pivotTable)
  {
    iset key | Route(node.pivotTable, key) == slotIndex && key in keys
  }

  function IFlush(flush: P.NodeFlush) : B.NodeFlush
  requires P.ValidFlush(flush)
  {
    B.NodeFlush(flush.parentref, INode(flush.parent), flush.childref, INode(flush.child), flush.newchildref, MovedKeys(flush.parent, flush.slotIndex), FlushedKeys(flush.parent, flush.slotIndex, flush.keys))
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
  requires 0 <= idx < |lookup|
  requires var lookupUpperBound := P.LookupUpperBound(lookup, startKey);
    && (lookupUpperBound.Some? ==> Keyspace.lt(key, lookupUpperBound.value))
  ensures var r := Route(lookup[idx].node.pivotTable, startKey);
      r < |lookup[idx].node.pivotTable| ==> Keyspace.lt(key, lookup[idx].node.pivotTable[r]);
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
  ensures Keyspace.lt(a, b)
  {
    match end {
      case EInclusive(key) => {
        assert Keyspace.lte(a, key);
        assert Keyspace.lt(key, b);
      }
      case EExclusive(key) => {
        assert Keyspace.lt(a, key);
        assert Keyspace.lte(key, b);
      }
      case PositiveInf => { }
    }
  }

  lemma InRangeImpliesSameRoute(start: MS.UI.RangeStart, key: Key, end: MS.UI.RangeEnd, lookup: P.Lookup, idx: int)
  requires MS.InRange(start, key, end)
  requires P.LookupVisitsWFNodes(lookup)
  requires
    var startKey := if start.NegativeInf? then [] else start.key;
    var lookupUpperBound := P.LookupUpperBound(lookup, startKey);
    && P.WFLookupForKey(lookup, startKey)
    && (lookupUpperBound.Some? ==> !MS.UpperBound(lookupUpperBound.value, end))
  requires 0 <= idx < |lookup|
  ensures var startKey := if start.NegativeInf? then [] else start.key;
        Route(lookup[idx].node.pivotTable, startKey)
     == Route(lookup[idx].node.pivotTable, key)
  {
    var startKey := if start.NegativeInf? then [] else start.key;

    var r := Route(lookup[idx].node.pivotTable, startKey);
    //assert r > 0 ==> Keyspace.lte(lookup[idx].node.pivotTable[r-1], startKey);

    Keyspace.EmptyLte(key);
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
    var lookupUpperBound := P.LookupUpperBound(lookup, startKey);
    && P.WFLookupForKey(lookup, startKey)
    && (lookupUpperBound.Some? ==> !MS.UpperBound(lookupUpperBound.value, end))
  ensures P.WFLookupForKey(lookup, key)
  {
    var startKey := if start.NegativeInf? then [] else start.key;

    forall idx | P.ValidLayerIndex(lookup, idx) && idx < |lookup| - 1 
    ensures P.LookupFollowsChildRefAtLayer(key, lookup, idx)
    {
      assert P.LookupFollowsChildRefAtLayer(startKey, lookup, idx);
      InRangeImpliesSameRoute(start, key, end, lookup, idx);
    }
  }

  lemma InterpretBucketStackEqInterpretLookupIter(
      start: MS.UI.RangeStart, end: MS.UI.RangeEnd, startKey: Key,
      buckets: seq<Bucket>, lookup: P.Lookup, key: Key,
      j: int)
  requires startKey == if start.NegativeInf? then [] else start.key;
  requires P.LookupVisitsWFNodes(lookup)
  requires |lookup| == |buckets|
  requires (forall i | 0 <= i < |lookup| :: buckets[i] == lookup[i].node.buckets[Route(lookup[i].node.pivotTable, startKey)])
  requires MS.InRange(start, key, end)
  requires
    var lookupUpperBound := P.LookupUpperBound(lookup, startKey);
    && P.WFLookupForKey(lookup, startKey)
    && (lookupUpperBound.Some? ==> !MS.UpperBound(lookupUpperBound.value, end))
  requires 0 <= j <= |lookup|
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
  requires |lookup| == |buckets|
  requires (forall i | 0 <= i < |lookup| :: buckets[i] == lookup[i].node.buckets[Route(lookup[i].node.pivotTable, startKey)])
  requires MS.InRange(start, key, end)
  requires
    var lookupUpperBound := P.LookupUpperBound(lookup, startKey);
    && P.WFLookupForKey(lookup, startKey)
    && (lookupUpperBound.Some? ==> !MS.UpperBound(lookupUpperBound.value, end))
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
  requires results ==
        SortedSeqOfKeyValueMap(
          KeyValueMapOfBucket(
            ClampRange(ComposeSeq(buckets), start, end)))
  ensures (forall i | 0 <= i < |results| ::
      P.BufferDefinesValue(InterpretBucketStack(buckets, results[i].key), results[i].value))
  ensures (forall i | 0 <= i < |results| :: results[i].value != MS.EmptyValue())
  ensures (forall i | 0 <= i < |results| :: MS.InRange(start, results[i].key, end))
  ensures (forall i, j | 0 <= i < j < |results| :: Keyspace.lt(results[i].key, results[j].key))
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
      SortedSeqOfKeyValueMaps(KeyValueMapOfBucket(ClampRange(ComposeSeq(buckets), start, end)), i);
      reveal_KeyValueMapOfBucket();
      reveal_ClampRange();

      //var m := ComposeSeq(buckets)[results[i].key];
      //assert Merge(m, M.DefineDefault()).value == results[i].value;
      BucketGetComposeSeq(buckets, results[i].key);
      //assert m == InterpretBucketStack(buckets, results[i].key);
    }

    SortedSeqOfKeyValueMapHasSortedKeys(KeyValueMapOfBucket(
            ClampRange(ComposeSeq(buckets), start, end)));

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
        SortedSeqOfKeyValueHasKey(KeyValueMapOfBucket(ClampRange(ComposeSeq(buckets), start, end)), key);
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
  requires ReadOpsBucketsWellMarshalled(P.FlushReads(flush))
  ensures B.ValidFlush(IFlush(flush))
  {
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
  requires node' == P.CutoffNodeAndKeepLeft(node, pivot);
  requires Keyspace.lt(key, pivot);
  ensures IBuffer(node)[key] == IBuffer(node')[key]
  ensures IMapsAgreeOnKey(IChildren(node), IChildren(node'), key)
  {
    reveal_SplitBucketLeft();
    P.reveal_CutoffNodeAndKeepLeft();
    var i := Route(node'.pivotTable, key);

    var cLeft := CutoffForLeft(node.pivotTable, pivot);
    if i < |node.pivotTable| {
      if i < cLeft - 1 {
        assert Keyspace.lt(key, node'.pivotTable[i]);
        assert Keyspace.lt(key, node.pivotTable[i]);
      } else {
        assert Keyspace.lt(key, node.pivotTable[i]);
      }
    }
    RouteIs(node.pivotTable, key, i);
  }

  lemma CutoffNodeAndKeepRightAgree(node: PNode, node': PNode, pivot: Key, key: Key)
  requires P.WFNode(node)
  requires P.WFNode(node')
  requires BucketListWellMarshalled(node.buckets)
  requires node' == P.CutoffNodeAndKeepRight(node, pivot);
  requires Keyspace.lte(pivot, key);
  ensures IBuffer(node)[key] == IBuffer(node')[key]
  ensures IMapsAgreeOnKey(IChildren(node), IChildren(node'), key)
  {
    reveal_SplitBucketRight();
    P.reveal_CutoffNodeAndKeepRight();
    var i := Route(node'.pivotTable, key);
    RouteIs(node.pivotTable, key, i + |node.pivotTable| - |node'.pivotTable|);
  }

  lemma CutoffNodeAgree(node: PNode, node': PNode, l: Option<Key>, r: Option<Key>, key: Key)
  requires P.WFNode(node)
  requires P.WFNode(node')
  requires BucketListWellMarshalled(node.buckets)
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
        PivotBetreeSpecWFNodes.BucketListWellMarshalledCutoffNodeAndKeepLeft(node, r.value);
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
  requires BucketListWellMarshalled(node.buckets)
  requires |node'.buckets| == |node.buckets| + 1
  requires 0 <= idx < |node.buckets|
  requires forall i | 0 <= i < idx :: node.buckets[i] == node'.buckets[i]
  //requires node.buckets[idx] == map[]
  //requires node'.buckets[idx] == map[]
  //requires node'.buckets[idx+1] == map[]
  requires node'.buckets[idx].b == SplitBucketLeft(node.buckets[idx], node'.pivotTable[idx]).b
  requires node'.buckets[idx+1].b == SplitBucketRight(node.buckets[idx], node'.pivotTable[idx]).b
  requires forall i | idx + 2 <= i < |node'.buckets| :: node'.buckets[i] == node.buckets[i-1]
  requires forall i | 0 <= i < idx :: node.pivotTable[i] == node'.pivotTable[i]
  requires forall i | idx < i < |node'.pivotTable| :: node'.pivotTable[i] == node.pivotTable[i-1]
  requires node.children.Some?
  requires node'.children.Some?
  requires forall i | 0 <= i < idx :: node.children.value[i] == node'.children.value[i]
  requires forall i | idx + 2 <= i < |node'.buckets| :: node'.children.value[i] == node.children.value[i-1]
  ensures IBuffer(node) == IBuffer(node')
  ensures forall key:Key | key !in PivotTableBucketKeySet(node.pivotTable, idx) ::
      IChildren(node)[key] == IChildren(node')[key]
  {
    reveal_SplitBucketLeft();
    reveal_SplitBucketRight();
    forall key:Key
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
        assert IBuffer(node)[key] == IBuffer(node')[key];
        assert key in PivotTableBucketKeySet(node.pivotTable, idx);
      } else if (i == idx + 1) {
        if (idx + 1 < |node'.pivotTable|) {
          assert node'.pivotTable[idx+1] == node.pivotTable[idx];
        }
        RouteIs(node.pivotTable, key, idx);
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
  requires ReadOpsBucketsWellMarshalled(P.MergeReads(f))
  requires P.InvNode(f.split_parent)
  requires P.InvNode(f.left_child)
  requires P.InvNode(f.right_child)
  ensures B.ValidRedirect(IMerge(f))
  {
    var redirect := IMerge(f);
    PivotBetreeSpecWFNodes.ValidMergeWritesInvNodes(f);

    assert P.WFNode(P.MergeOps(f)[0].node);
    assert P.WFNode(P.MergeOps(f)[1].node);

    assert P.MergeReads(f)[0].node == f.split_parent;
    assert BucketListWellMarshalled(f.split_parent.buckets);
    WellMarshalledMergeBucketsInList(f.split_parent.buckets, f.slot_idx);

    forall ref | ref in IMapRestrict(redirect.old_parent.children, redirect.keys).Values
    ensures ref in redirect.old_childrefs
    {
      var key: Key :| IMapsTo(IMapRestrict(redirect.old_parent.children, redirect.keys), key, ref);
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

    reveal_MergeBucketsInList();
    SplitOfMergeBucketsInList(f.split_parent.buckets, f.slot_idx, f.split_parent.pivotTable);
    SplitMergeBuffersChildrenEq(f.fused_parent, f.split_parent, f.slot_idx);

    var lb := (if f.slot_idx > 0 then Some(f.split_parent.pivotTable[f.slot_idx - 1]) else None);
    var ub := (if f.slot_idx + 1 < |f.split_parent.pivotTable| then Some(f.split_parent.pivotTable[f.slot_idx + 1]) else None);
    var l := P.CutoffNode(f.left_child, lb , Some(f.pivot));
    var r := P.CutoffNode(f.right_child, Some(f.pivot), ub);

    assert redirect.old_children[f.left_childref] == INode(f.left_child);
    assert redirect.old_children[f.right_childref] == INode(f.right_child);

    forall key:Key | key in redirect.keys * redirect.old_parent.children.Keys
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

    reveal_SplitBucketInList();
    SplitMergeBuffersChildrenEq(f.fused_parent, f.split_parent, f.slot_idx);

    var lbound := (if f.slot_idx > 0 then Some(f.fused_parent.pivotTable[f.slot_idx - 1]) else None);
    var ubound := (if f.slot_idx < |f.fused_parent.pivotTable| then Some(f.fused_parent.pivotTable[f.slot_idx]) else None);
    var ch := P.CutoffNode(f.fused_child, lbound, ubound);

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
            BucketGet(oldroot.buckets[Route(oldroot.pivotTable, ins.key)], ins.key),
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

  lemma AddMessagesToNodeResult(node: PNode, bucket: Bucket, node': PNode, key: Key)
  requires P.InvNode(node)
  requires BucketWellMarshalled(bucket)
  requires BucketListWellMarshalled(node.buckets)
  requires node' == P.AddMessagesToNode(node, bucket);
  ensures WFBucketListProper(node'.buckets, node'.pivotTable);
  ensures key !in bucket.b ==> P.NodeLookup(node', key) == P.NodeLookup(node, key)
  ensures key in bucket.b ==> P.NodeLookup(node', key) == Merge(bucket.b[key], P.NodeLookup(node, key))
  {
    GetBucketListFlushEqMerge(bucket, node.buckets, node.pivotTable, key);
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

    var comp := BucketComplement(flush.parent.buckets[flush.slotIndex], flush.keys);
    var isec := BucketIntersect(flush.parent.buckets[flush.slotIndex], flush.keys);

    var newparent := P.G.Node(
        flush.parent.pivotTable,
        Some(flush.parent.children.value[flush.slotIndex := flush.newchildref]),
        flush.parent.buckets[flush.slotIndex := comp]
      );
    var newchild := P.AddMessagesToNode(flush.child, isec);
    var allocop := P.G.AllocOp(flush.newchildref, newchild);
    var writeop := P.G.WriteOp(flush.parentref, newparent);

    assert P.WFNode(newchild);
    assert P.WFNode(newparent);

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
    var newbuffer := imap k:Key :: (if k in flush'.flushedKeys then Merge(parent.buffer[k], child.buffer[k]) else child.buffer[k]);
    var newchild' := B.G.Node(child.children, newbuffer);
    var newparentbuffer := imap k:Key :: (if k in flush'.flushedKeys then Update(NopDelta()) else parent.buffer[k]);
    var newparentchildren := imap k:Key | k in parent.children :: (if k in flush'.movedKeys then newchildref else parent.children[k]);
    var newparent' := B.G.Node(newparentchildren, newparentbuffer);
    var allocop' := B.G.AllocOp(newchildref, newchild');
    var writeop' := B.G.WriteOp(parentref, newparent');

    reveal_BucketIntersect();
    reveal_BucketComplement();

    forall k: Key
    ensures IBuffer(newchild)[k] == newbuffer[k]
    {
      AddMessagesToNodeResult(flush.child, isec, newchild, k);
      if (k in flush'.flushedKeys) {
        //RouteIs(flush.parent.pivotTable, k, flush.slotIndex);
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

    forall k: Key
    ensures IChildren(newparent)[k] == newparent'.children[k]
    {
      if (k in flush'.flushedKeys) {
        RouteIs(flush.parent.pivotTable, k, flush.slotIndex);
        assert IChildren(newparent)[k] == newparent'.children[k];
      } else if k in flush'.movedKeys {
        assert IChildren(newparent)[k] == newparent'.children[k];
      } else {
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

    var newroot := P.G.Node([], Some([growth.newchildref]), [BucketsLib.B(map[])]);
    var newroot' := B.G.Node(
        imap key | MS.InDomain(key) :: IGrow(growth).newchildref,
        imap key | MS.InDomain(key) :: Update(NopDelta()));
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

  lemma IBufferLeafEqJoin(node: PNode)
  requires P.InvNode(node)
  requires BucketListWellMarshalled(node.buckets)
  ensures IBufferLeaf(node) == imap key :: Merge(BucketGet(JoinBucketList(node.buckets), key), DefineDefault())
  {
    forall key:Key
    ensures IBufferLeaf(node)[key] == Merge(BucketGet(JoinBucketList(node.buckets), key), DefineDefault())
    {
      forall i | 0 <= i < |node.buckets| ensures WFBucketAt(node.buckets[i], node.pivotTable, i)
      {
        //assert P.NodeHasWFBucketAt(node, i);
      }
      GetJoinBucketListEq(node.buckets, node.pivotTable, key);
      //assert BucketGet(node.buckets[Route(node.pivotTable, key)], key) == BucketGet(JoinBucketList(node.buckets), key);
    }
  }

  lemma RepivotPreservesNode(r: P.Repivot)
  requires P.ValidRepivot(r)
  requires forall i | 0 <= i < |P.RepivotReads(r)| :: P.InvNode(P.RepivotReads(r)[i].node)
  ensures P.InvNode(P.ApplyRepivot(r.leaf, r.pivots))
  ensures INode(r.leaf) == INode(P.ApplyRepivot(r.leaf, r.pivots))
  {
    assert P.InvNode(P.RepivotReads(r)[0].node);
    PivotBetreeSpecWFNodes.InvApplyRepivot(r.leaf, r.pivots);

    var buckets1 := r.leaf.buckets;
    var joined := JoinBucketList(buckets1);
    WFJoinBucketList(buckets1);

    var buckets2 := SplitBucketOnPivots(joined, r.pivots);
    WFSplitBucketOnPivots(joined, r.pivots);

    forall i | 0 <= i < |buckets1|
    ensures forall key:Key | key in buckets1[i].b :: buckets1[i].b[key] != IdentityMessage()
    {
      //assert P.NodeHasWFBucketAt(r.leaf, i);
    }
    WFJoinBucketList(r.leaf.buckets);
    JoinBucketsSplitBucketOnPivotsCancel(joined, r.pivots);
    assert JoinBucketList(buckets1) == JoinBucketList(buckets2);
    
    IBufferLeafEqJoin(r.leaf);
    IBufferLeafEqJoin(P.ApplyRepivot(r.leaf, r.pivots));
  }
}
