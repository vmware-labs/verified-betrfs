include "StateModel.i.dfy"
include "BookkeepingModel.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sets.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "BucketSuccessorLoopModel.i.dfy"

// See dependency graph in MainHandlers.dfy

module SuccModel { 
  import opened StateModel
  import opened IOModel
  import opened BookkeepingModel
  import opened KeyType
  import opened ViewOp
  import opened InterpretationDiskOps
  import opened DiskOpModel

  import opened Options
  import opened Maps
  import opened Sets
  import opened Sequences
  import opened NativeTypes

  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds

  import opened BoundedPivotsLib
  import opened Lexicographic_Byte_Order
  import BucketSuccessorLoopModel

  import PBS = PivotBetreeSpec`Internal

  // Awkwardly split up for verification time reasons

  function {:opaque} getPathInternal(
      
      s: BCVariables,
      io: IO,
      key: Key,
      acc: seq<Bucket>,
      start: UI.RangeStart,
      upTo: Option<Key>,
      maxToFind: int,
      ref: BT.G.Reference,
      counter: uint64,
      node: Node)
  : (res : (BCVariables, IO, Option<UI.SuccResultList>))
  requires BCInv(s)
  requires s.Ready?
  requires io.IOInit?
  requires WFNode(node)
  requires ref in s.cache
  requires ref in s.ephemeralIndirectionTable.graph
  requires node == s.cache[ref]
  requires maxToFind >= 1
  requires BoundedKey(node.pivotTable, key)
  requires forall i | 0 <= i < |acc| :: WFBucket(acc[i])
  ensures var (s', io, sr) := res;
    && s'.Ready?
    && WFBCVars(s')
    && s'.cache == s.cache
  decreases counter, 0
  {
    var r := Route(node.pivotTable, key);
    var bucket := node.buckets[r];
    var acc' := acc + [bucket];

    var pivot := node.pivotTable[r+1];
    var upTo' := 
      if pivot.Max_Element?
      then (
        upTo
      ) else (
        var ub := GetKey(node.pivotTable, r+1);
        if upTo.Some?
        then (
          var k: Key := if lt(upTo.value, ub) then upTo.value else ub;
          Some(k)
        ) else (
          Some(ub)
        )
      );

    if node.children.Some? then (
      if counter == 0 then (
        (s, io, None)
      ) else (
        lemmaChildInGraph(s, ref, node.children.value[r]);
        getPath(s, io, key, acc', start, upTo', maxToFind, node.children.value[r], counter - 1)
      )
    ) else (
      var res :=
          BucketSuccessorLoopModel.GetSuccessorInBucketStack(acc', maxToFind, start, upTo');
      (s, io, Some(res))
    )
  }

  function {:opaque} getPath(
      
      s: BCVariables,
      io: IO,
      key: Key,
      acc: seq<Bucket>,
      start: UI.RangeStart,
      upTo: Option<Key>,
      maxToFind: int,
      ref: BT.G.Reference,
      counter: uint64)
  : (res : (BCVariables, IO, Option<UI.SuccResultList>))
  requires BCInv(s)
  requires s.Ready?
  requires io.IOInit?
  requires maxToFind >= 1
  requires ref in s.ephemeralIndirectionTable.graph
  requires forall i | 0 <= i < |acc| :: WFBucket(acc[i])
  ensures var (s', io, sr) := res;
    && s'.Ready?
    && WFBCVars(s')
    && s'.cache == s.cache
  decreases counter, 1
  {
    if ref in s.cache then (
      var node := s.cache[ref];
      if BoundedKey(node.pivotTable, key) then ( 
        var (s0, io', pr) := getPathInternal(s, io, key, acc, start, upTo, maxToFind, ref, counter, node);
        LruModel.LruUse(s0.lru, ref);
        var s' := s0.(lru := LruModel.Use(s0.lru, ref));
        assert WFBCVars(s');
        (s', io', pr)
      ) else (
        (s, io, None)
      )
    ) else (
      if TotalCacheSize(s) <= MaxCacheSize() - 1 then (
        var (s', io') := PageInNodeReq(s, io, ref);
        assert WFBCVars(s');
        (s', io', None)
      ) else (
        (s, io, None)
      )
    )
  }

  function {:opaque} doSucc(s: BCVariables, io: IO, start: UI.RangeStart, maxToFind: int)
  : (res : (BCVariables, IO, Option<UI.SuccResultList>))
  requires BCInv(s)
  requires io.IOInit?
  requires s.Ready?
  requires maxToFind >= 1
  {
    var startKey := if start.NegativeInf? then [] else start.key;
    getPath(s, io, startKey, [], start, None, maxToFind, BT.G.Root(), 40)
  }

  /////////////////////////////////
  /////////////////////////////////
  ///////////////////////////////// Proof stuff
  /////////////////////////////////
  /////////////////////////////////

  predicate LookupBucketsProps(lookup: PBS.Lookup, buckets: seq<Bucket>, upTo: Option<Key>, startKey: Key)
  {
    && PBS.WFLookupForKey(lookup, startKey)
    && upTo == PBS.LookupUpperBound(lookup, startKey)
    && Last(lookup).node.children.None?
    && |lookup| == |buckets|
    && (forall i | 0 <= i < |lookup| :: BoundedKey(lookup[i].node.pivotTable, startKey))
    && (forall i | 0 <= i < |lookup| :: buckets[i] == lookup[i].node.buckets[Route(lookup[i].node.pivotTable, startKey)])
  }

  lemma SatisfiesSuccBetreeStep(s: BCVariables, io: IO, start: UI.RangeStart,
      res: UI.SuccResultList, buckets: seq<Bucket>, lookup: PBS.Lookup, maxToFind: int, startKey: Key, upTo: Option<Key>)
  requires BCInv(s)
  requires s.Ready?
  requires io.IOInit?
  requires maxToFind >= 1
  requires LookupBucketsProps(lookup, buckets, upTo, startKey);
  requires forall i | 0 <= i < |lookup| :: lookup[i].ref in IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires forall i | 0 <= i < |lookup| :: MapsTo(ICache(s.cache), lookup[i].ref, lookup[i].node)
  requires (upTo.Some? ==> lt(startKey, upTo.value))
  requires startKey == (if start.NegativeInf? then [] else start.key)
  requires res == 
     BucketSuccessorLoopModel.GetSuccessorInBucketStack(buckets, maxToFind, start, upTo);

  ensures ValidDiskOp(diskOp(io))
  ensures BBC.Next(IBlockCache(s), IBlockCache(s),
      IDiskOp(diskOp(io)).bdop,
      AdvanceOp(UI.SuccOp(start, res.results, res.end), false));
  {
    if (BucketListWellMarshalled(buckets)) {
      BucketSuccessorLoopModel.GetSuccessorInBucketStackResult(buckets, maxToFind, start, upTo);
    }

    var succStep := BT.SuccQuery(start, res.results, res.end, buckets, lookup);
    assert BT.ValidSuccQuery(succStep);
    var step := BT.BetreeSuccQuery(succStep);

    assert BBC.BetreeMove(IBlockCache(s), IBlockCache(s),
      IDiskOp(diskOp(io)).bdop,
      AdvanceOp(UI.SuccOp(start, res.results, res.end), false),
      step);
    assert stepsBetree(IBlockCache(s), IBlockCache(s),
      AdvanceOp(UI.SuccOp(start, res.results, res.end), false),
      step);
  }

  lemma lemmaGetPathResult(s: BCVariables, io: IO, startKey: Key, acc: seq<Bucket>, lookup: PBS.Lookup, start: UI.RangeStart, upTo: Option<Key>, maxToFind: int, ref: BT.G.Reference, counter: uint64)
  requires BCInv(s)
  requires s.Ready?
  requires io.IOInit?
  requires maxToFind >= 1
  requires forall i | 0 <= i < |acc| :: WFBucket(acc[i])
  requires ref in s.ephemeralIndirectionTable.graph
  requires |lookup| > 0 ==> PBS.WFLookupForKey(lookup, startKey)
  requires |lookup| > 0 ==> Last(lookup).node.children.Some?
  requires |lookup| > 0 ==> ref == Last(lookup).node.children.value[Route(Last(lookup).node.pivotTable, startKey)]
  requires |lookup| == 0 ==> ref == BT.G.Root()
  requires upTo == PBS.LookupUpperBound(lookup, startKey)
  requires |lookup| == |acc|
  requires forall i | 0 <= i < |lookup| :: acc[i] == lookup[i].node.buckets[Route(lookup[i].node.pivotTable, startKey)]
  requires (forall i | 0 <= i < |lookup| :: lookup[i].ref in IIndirectionTable(s.ephemeralIndirectionTable).graph)
  requires forall i | 0 <= i < |lookup| :: lookup[i].ref in s.cache && lookup[i].node == INode(s.cache[lookup[i].ref])
  requires upTo.Some? ==> lt(startKey, upTo.value)
  requires startKey == (if start.NegativeInf? then [] else start.key)
  decreases counter
  ensures var (s', io', res) := getPath(s, io, startKey, acc, start, upTo, maxToFind, ref, counter);
      && WFBCVars(s')
      && ValidDiskOp(diskOp(io'))
      && IDiskOp(diskOp(io')).jdop.NoDiskOp?
      && (res.Some? ==> BBC.Next(IBlockCache(s), IBlockCache(s'),
            IDiskOp(diskOp(io')).bdop,
            AdvanceOp(UI.SuccOp(start, res.value.results, res.value.end), false)))
      && (res.None? ==>
            betree_next_dop(IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop))
    /*  && IBlockCache(s1) == IBlockCache(s)
      && s1.ephemeralIndirectionTable == s.ephemeralIndirectionTable
      && (pr.Fetch? ==> pr.ref in s.ephemeralIndirectionTable.locs)
      && (pr.Fetch? ==> pr.ref !in s.cache)
      && (pr.Path? ==> (
        && LookupBucketsProps(lookup', pr.buckets, pr.upTo, startKey))
        && (forall i | 0 <= i < |lookup'| :: lookup'[i].ref in IIndirectionTable(s.ephemeralIndirectionTable).graph)
        && (forall i | 0 <= i < |lookup'| :: MapsTo(ICache(s.cache), lookup'[i].ref, lookup'[i].node))
        && (pr.upTo.Some? ==> lt(startKey, pr.upTo.value))
      ) */
  {
    reveal_getPath();
    reveal_getPathInternal();

    if ref in s.cache {
      var node := s.cache[ref];
      if BoundedKey(node.pivotTable, startKey) {
        var r := Pivots.Route(node.pivotTable, startKey);
        var bucket := node.buckets[r];
        var acc1 := acc + [bucket];
        var lookup1 := lookup + [BT.G.ReadOp(ref, INode(node))];

        forall idx | PBS.ValidLayerIndex(lookup1, idx) && idx < |lookup1| - 1
        ensures PBS.LookupFollowsChildRefAtLayer(startKey, lookup1, idx)
        {
          if idx == |lookup1| - 2 {
            assert PBS.LookupFollowsChildRefAtLayer(startKey, lookup1, idx);
          } else {
            assert PBS.LookupFollowsChildRefAtLayer(startKey, lookup, idx);
            assert PBS.LookupFollowsChildRefAtLayer(startKey, lookup1, idx);
          }
        }

        var pivot := node.pivotTable[r+1];
        var upTo' := 
          if pivot.Max_Element? then (
            upTo
          ) else (
            var ub := GetKey(node.pivotTable, r+1);
            if upTo.Some?
            then (
              var k: Key := if lt(upTo.value, ub) then upTo.value else ub;
              Some(k)
            ) else (
              Some(ub)
            )
          );

        assert upTo'.Some? ==> lt(startKey, upTo'.value);

        PBS.reveal_LookupUpperBound();

        if node.children.Some? {
          if counter == 0 {
            assert noop(IBlockCache(s), IBlockCache(s));
          } else {
            lemmaChildInGraph(s, ref, node.children.value[r]);
            lemmaGetPathResult(s, io, startKey, acc1, lookup1, start, upTo', maxToFind, node.children.value[r], counter - 1);
          }
        } else {
          var res :=
            BucketSuccessorLoopModel.GetSuccessorInBucketStack(acc1, maxToFind, start, upTo');
          SatisfiesSuccBetreeStep(s, io, start, res, acc1, lookup1, maxToFind, startKey, upTo');
        }
      } else {
        assert noop(IBlockCache(s), IBlockCache(s));
      }
    } else {
      if TotalCacheSize(s) <= MaxCacheSize() - 1 {
        assert ref in s.ephemeralIndirectionTable.graph;
        assert ref in s.ephemeralIndirectionTable.locs;
        PageInNodeReqCorrect(s, io, ref);
      } else {
        assert noop(IBlockCache(s), IBlockCache(s));
      }
    }
  }

  lemma doSuccCorrect(s: BCVariables, io: IO, start: UI.RangeStart, maxToFind: int)
  requires BCInv(s)
  requires io.IOInit?
  requires maxToFind >= 1
  requires s.Ready?
  ensures var (s', io', res) := doSucc(s, io, start, maxToFind);
    && WFBCVars(s')
    && ValidDiskOp(diskOp(io'))
    && IDiskOp(diskOp(io')).jdop.NoDiskOp?
    && (res.Some? ==> BBC.Next(IBlockCache(s), IBlockCache(s'),
            IDiskOp(diskOp(io')).bdop,
            AdvanceOp(UI.SuccOp(start, res.value.results, res.value.end), false)))
    && (res.None? ==>
            betree_next_dop(IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop))
  {
    reveal_doSucc();
    PBS.reveal_LookupUpperBound();
    var startKey := if start.NegativeInf? then [] else start.key;
    lemmaGetPathResult(s, io, startKey, [], [], start, None, maxToFind, BT.G.Root(), 40);
  }
}
