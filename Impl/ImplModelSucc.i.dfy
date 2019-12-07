include "ImplModel.i.dfy"
include "ImplModelCache.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sets.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "ModelBucket.i.dfy"
include "../PivotBetree/BucketSuccessorLoop.i.dfy"

// See dependency graph in MainImpl.dfy

module ImplModelSucc { 
  import opened ImplModel
  import opened ImplModelIO
  import opened ImplModelCache

  import opened Options
  import opened Maps
  import opened Sets
  import opened Sequences
  import opened NativeTypes

  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds
  import PivotsLib

  import opened ModelBucket
  import opened Lexicographic_Byte_Order
  import BucketSuccessorLoop

  import PBS = PivotBetreeSpec`Internal

  // Awkwardly split up for verification time reasons

  function {:opaque} getPathInternal(
      k: Constants,
      s: Variables,
      io: IO,
      key: Key,
      acc: seq<Bucket>,
      start: UI.RangeStart,
      upTo: Option<Key>,
      maxToFind: int,
      ref: BT.G.Reference,
      counter: uint64,
      node: Node)
  : (res : (Variables, IO, Option<UI.SuccResultList>))
  requires Inv(k, s)
  requires s.Ready?
  requires io.IOInit?
  requires WFNode(node)
  requires ref in s.cache
  requires ref in s.ephemeralIndirectionTable.graph
  requires node == s.cache[ref]
  requires maxToFind >= 1
  ensures var (s', io, sr) := res;
    && s'.Ready?
    && WFVars(s')
    && s'.cache == s.cache
  decreases counter, 0
  {
    var r := Pivots.Route(node.pivotTable, key);
    var bucket := node.buckets[r];
    var acc' := acc + [bucket];
    var upTo' := 
      if r == |node.pivotTable| then (
        upTo
      ) else (
        var ub := node.pivotTable[r];
        if upTo.Some? then (
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
        lemmaChildInGraph(k, s, ref, node.children.value[r]);
        getPath(k, s, io, key, acc', start, upTo', maxToFind, node.children.value[r], counter - 1)
      )
    ) else (
      var res :=
          BucketSuccessorLoop.GetSuccessorInBucketStack(acc', maxToFind, start, upTo');
      (s, io, Some(res))
    )
  }

  function {:opaque} getPath(
      k: Constants,
      s: Variables,
      io: IO,
      key: Key,
      acc: seq<Bucket>,
      start: UI.RangeStart,
      upTo: Option<Key>,
      maxToFind: int,
      ref: BT.G.Reference,
      counter: uint64)
  : (res : (Variables, IO, Option<UI.SuccResultList>))
  requires Inv(k, s)
  requires s.Ready?
  requires io.IOInit?
  requires maxToFind >= 1
  requires ref in s.ephemeralIndirectionTable.graph
  ensures var (s', io, sr) := res;
    && s'.Ready?
    && WFVars(s')
    && s'.cache == s.cache
  decreases counter, 1
  {
    if ref in s.cache then (
      var node := s.cache[ref];
      var (s0, io', pr) := getPathInternal(k, s, io, key, acc, start, upTo, maxToFind, ref, counter, node);

      LruModel.LruUse(s0.lru, ref);
      var s' := s0.(lru := LruModel.Use(s0.lru, ref));

      assert WFVars(s');
      (s', io', pr)
    ) else (
      if TotalCacheSize(s) <= MaxCacheSize() - 1 then (
        var (s', io') := PageInReq(k, s, io, ref);
        assert WFVars(s');
        (s', io', None)
      ) else (
        (s, io, None)
      )
    )
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
    && (forall i | 0 <= i < |lookup| :: buckets[i] == lookup[i].node.buckets[Pivots.Route(lookup[i].node.pivotTable, startKey)])
  }

  lemma SatisfiesSuccBetreeStep(k: Constants, s: Variables, io: IO, start: UI.RangeStart,
      res: UI.SuccResultList, buckets: seq<Bucket>, lookup: PBS.Lookup, maxToFind: int, startKey: Key, upTo: Option<Key>)
  requires Inv(k, s)
  requires s.Ready?
  requires io.IOInit?
  requires maxToFind >= 1
  requires LookupBucketsProps(lookup, buckets, upTo, startKey);
  requires forall i | 0 <= i < |lookup| :: lookup[i].ref in IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires forall i | 0 <= i < |lookup| :: MapsTo(ICache(s.cache), lookup[i].ref, lookup[i].node)
  requires (upTo.Some? ==> lt(startKey, upTo.value))
  requires startKey == (if start.NegativeInf? then [] else start.key)
  requires res == 
     BucketSuccessorLoop.GetSuccessorInBucketStack(buckets, maxToFind, start, upTo);

  ensures M.Next(Ik(k), IVars(s), IVars(s),
      UI.SuccOp(start, res.results, res.end),
      diskOp(io))
  {
    BucketSuccessorLoop.GetSuccessorInBucketStackResult(buckets, maxToFind, start, upTo);

    var succStep := BT.SuccQuery(start, res.results, res.end, buckets, lookup);
    assert BT.ValidSuccQuery(succStep);
    var step := BT.BetreeSuccQuery(succStep);

    assert BBC.BetreeMove(Ik(k), IVars(s), IVars(s),
      UI.SuccOp(start, res.results, res.end),
      M.IDiskOp(diskOp(io)),
      step);
    assert stepsBetree(k, IVars(s), IVars(s),
      UI.SuccOp(start, res.results, res.end),
      step);

    assert M.Next(Ik(k), IVars(s), IVars(s),
      UI.SuccOp(start, res.results, res.end),
      diskOp(io));
  }

  lemma lemmaGetPathResult(k: Constants, s: Variables, io: IO, startKey: Key, acc: seq<Bucket>, lookup: PBS.Lookup, start: UI.RangeStart, upTo: Option<Key>, maxToFind: int, ref: BT.G.Reference, counter: uint64)
  requires Inv(k, s)
  requires s.Ready?
  requires io.IOInit?
  requires maxToFind >= 1
  requires ref in s.ephemeralIndirectionTable.graph
  requires |lookup| > 0 ==> PBS.WFLookupForKey(lookup, startKey)
  requires |lookup| > 0 ==> Last(lookup).node.children.Some?
  requires |lookup| > 0 ==> ref == Last(lookup).node.children.value[Pivots.Route(Last(lookup).node.pivotTable, startKey)]
  requires |lookup| == 0 ==> ref == BT.G.Root()
  requires upTo == PBS.LookupUpperBound(lookup, startKey)
  requires |lookup| == |acc|
  requires forall i | 0 <= i < |lookup| :: acc[i] == lookup[i].node.buckets[Pivots.Route(lookup[i].node.pivotTable, startKey)]
  requires (forall i | 0 <= i < |lookup| :: lookup[i].ref in IIndirectionTable(s.ephemeralIndirectionTable).graph)
  requires forall i | 0 <= i < |lookup| :: lookup[i].ref in s.cache && lookup[i].node == INode(s.cache[lookup[i].ref])
  requires upTo.Some? ==> lt(startKey, upTo.value)
  requires startKey == (if start.NegativeInf? then [] else start.key)
  decreases counter
  ensures var (s', io', res) := getPath(k, s, io, startKey, acc, start, upTo, maxToFind, ref, counter);
      && WFVars(s')
      && M.Next(Ik(k), IVars(s), IVars(s'),
          if res.Some? then UI.SuccOp(start, res.value.results, res.value.end) else UI.NoOp,
          diskOp(io'))
    /*  && IVars(s1) == IVars(s)
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

      var upTo' := 
        if r == |node.pivotTable| then (
          upTo
        ) else (
          var ub := node.pivotTable[r];
          if upTo.Some? then (
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
          assert noop(k, IVars(s), IVars(s));
        } else {
          lemmaChildInGraph(k, s, ref, node.children.value[r]);

          lemmaGetPathResult(k, s, io, startKey, acc1, lookup1, start, upTo', maxToFind, node.children.value[r], counter - 1);
        }
      } else {
        var res :=
          BucketSuccessorLoop.GetSuccessorInBucketStack(acc1, maxToFind, start, upTo');
        SatisfiesSuccBetreeStep(k, s, io, start, res, acc1, lookup1, maxToFind, startKey, upTo');
      }
    } else {
      if TotalCacheSize(s) <= MaxCacheSize() - 1 {
        assert ref in s.ephemeralIndirectionTable.graph;
        assert ref in s.ephemeralIndirectionTable.locs;
        PageInReqCorrect(k, s, io, ref);
      } else {
        assert noop(k, IVars(s), IVars(s));
      }
    }
  }

  /*
  lemma doSuccCorrect(k: Constants, s: Variables, io: IO, start: UI.RangeStart, maxToFind: int)
  requires Inv(k, s)
  requires io.IOInit?
  requires maxToFind >= 1
  ensures var (s', io', res) := doSucc(k, s, io, start, maxToFind);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'),
        if res.Some? then UI.SuccOp(start, res.value.results, res.value.end) else UI.NoOp,
        diskOp(io'))
  {
    reveal_doSucc();

    if (s.Unready?) {
      PageInIndirectionTableReqCorrect(k, s, io);
    } else {
      var startKey := if start.NegativeInf? then [] else start.key;

      lemmaGetPathValidFetch(k, s, startKey, 40);
      var lookup := lemmaGetPathValidLookup(k, s, startKey, 40);
      var (s1, pr) := getPath(k, s, startKey, [], None, BT.G.Root(), 40);

      assert IVars(s) == IVars(s1);

      match pr {
        case Path(buckets, upTo) => {
          assert upTo.Some? ==> lt(startKey, upTo.value);

          var res :=
              BucketSuccessorLoop.GetSuccessorInBucketStack(buckets, maxToFind, start, upTo);
          BucketSuccessorLoop.GetSuccessorInBucketStackResult(buckets, maxToFind, start, upTo);

          var s' := s1;
          var io' := io;

          var succStep := BT.SuccQuery(start, res.results, res.end, buckets, lookup);
          assert BT.ValidSuccQuery(succStep);
          var step := BT.BetreeSuccQuery(succStep);

          assert BBC.BetreeMove(Ik(k), IVars(s), IVars(s'),
            UI.SuccOp(start, res.results, res.end),
            M.IDiskOp(diskOp(io)),
            step);
          assert stepsBetree(k, IVars(s), IVars(s'),
            UI.SuccOp(start, res.results, res.end),
            step);
        }
        case Fetch(ref) => {
          if TotalCacheSize(s1) <= MaxCacheSize() - 1 {
            PageInReqCorrect(k, s1, io, ref);
          } else {
            assert noop(k, IVars(s), IVars(s1));
          }
        }
        case Failure => {
          assert noop(k, IVars(s), IVars(s1));
        }
      }
    }
  }
  */
}
