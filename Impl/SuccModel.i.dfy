// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "BookkeepingModel.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sets.i.dfy"
include "BucketSuccessorLoopModel.i.dfy"

// See dependency graph in MainHandlers.dfy

module SuccModel { 
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
  import opened TranslationLib
  import opened Lexicographic_Byte_Order
  import BucketSuccessorLoopModel

  // Awkwardly split up for verification time reasons

  function NextPrefixSet(pivots: PivotTable, edges: EdgeTable, key: Key, pset: Option<PrefixSet>) : (pset': Option<PrefixSet>)
  requires WFPivots(pivots)
  requires WFEdges(edges, pivots)
  requires BoundedKey(pivots, key)
  requires pset.Some? ==> IsPrefix(pset.value.prefix, key)
  ensures pset'.Some? ==> IsPrefix(pset'.value.prefix, TranslateKey(pivots, edges, key))
  ensures ApplyPrefixSet(pset, key) == ApplyPrefixSet(pset', TranslateKey(pivots, edges, key))
  {
    reveal_IsPrefix();
    var translate := Translate(pivots, edges, key);
    assert translate.Some? ==> IsPrefix(translate.value.prefix, key);
    assert pset.Some? ==> IsPrefix(pset.value.prefix, key);

    var pset' := ComposePrefixSet(pset, translate);
    var key' := TranslateKey(pivots, edges, key);
    assert pset'.Some? ==> IsPrefix(pset'.value.prefix, key');
    ComposePrefixSetCorrect(pset, translate, pset', ApplyPrefixSet(pset, key), key, key');
    pset'
  }

  function {:opaque} {:timeLimitMultiplier 2} getPathInternal(
      s: BBC.Variables,
      io: IO,
      key: Key,
      acc: seq<Bucket>,
      tt: TranslationTable,
      start: UI.RangeStart,
      upTo: Option<Key>,
      pset: Option<PrefixSet>,
      maxToFind: int,
      ref: BT.G.Reference,
      counter: uint64,
      node: Node)
  : (res : (BBC.Variables, IO, Option<UI.SuccResultList>))
  requires BBC.Inv(s)
  requires s.Ready?
  requires io.IOInit?
  requires BT.WFNode(node)
  requires ref in s.cache
  requires ref in s.ephemeralIndirectionTable.graph
  requires node == s.cache[ref]
  requires maxToFind >= 1
  requires BoundedKey(node.pivotTable, key)
  requires forall i | 0 <= i < |acc| :: WFBucket(acc[i])
  requires |acc| == 0 ==> |tt| == 0 && pset == None
  requires |acc| > 0 ==> |tt| + 1 == |acc|
  requires var startKey := if start.NegativeInf? then [] else start.key;
    && (forall i | 0 <= i < |tt| :: 
        (tt[i].Some? ==> IsPrefix(tt[i].value.newPrefix, startKey)))
    && (pset.Some? ==> IsPrefix(pset.value.prefix, key))
    && startKey == ApplyPrefixSet(pset, key)
  ensures var (s', io, sr) := res;
    && s'.Ready?
    && s'.cache == s.cache
  decreases counter, 0
  {
    var startKey := if start.NegativeInf? then [] else start.key;

    var r := Route(node.pivotTable, key);
    var bucket := node.buckets[r];
    var acc' := acc + [bucket];
    var tt' := if |acc| == 0 then tt else tt + [pset];

    var upper := 
      if pset.None? then (
        node.pivotTable[r+1]
      ) else (
        var (_, right) := TranslatePivotPairInternal(KeyToElement(key), node.pivotTable[r+1], pset.value.prefix, pset.value.newPrefix);
        right
      );

    var upTo' := 
      if upper.Max_Element? then upTo 
      else (
        var ub : Key := upper.e;
        if upTo.None? then (
          Some(ub)
        ) else (
          var k: Key := if lt(upTo.value, upper.e) then upTo.value else ub;
          Some(k)
        ));

    if node.children.Some? then (
      if counter == 0 then (
        (s, io, None)
      ) else (
        var key' := TranslateKey(node.pivotTable, node.edgeTable, key);
        var pset' := NextPrefixSet(node.pivotTable, node.edgeTable, key, pset);

        lemmaChildInGraph(s, ref, node.children.value[r]);
        getPath(s, io, key', acc', tt', start, upTo', pset', maxToFind, node.children.value[r], counter - 1)
      )
    ) else (
      var res :=
          BucketSuccessorLoopModel.GetSuccessorInBucketStack(acc', tt', maxToFind, start, upTo');
      (s, io, Some(res))
    )
  }

  function {:opaque} getPath(
      s: BBC.Variables,
      io: IO,
      key: Key,
      acc: seq<Bucket>,
      tt: TranslationTable,
      start: UI.RangeStart,
      upTo: Option<Key>,
      pset: Option<PrefixSet>,
      maxToFind: int,
      ref: BT.G.Reference,
      counter: uint64)
  : (res : (BBC.Variables, IO, Option<UI.SuccResultList>))
  requires BBC.Inv(s)
  requires s.Ready?
  requires io.IOInit?
  requires maxToFind >= 1
  requires ref in s.ephemeralIndirectionTable.graph
  requires forall i | 0 <= i < |acc| :: WFBucket(acc[i])
  requires |acc| == 0 ==> |tt| == 0 && pset == None
  requires |acc| > 0 ==> |tt| + 1 == |acc|
  requires var startKey := if start.NegativeInf? then [] else start.key;
    && (forall i | 0 <= i < |tt| :: 
        (tt[i].Some? ==> IsPrefix(tt[i].value.newPrefix, startKey)))
    && (pset.Some? ==> IsPrefix(pset.value.prefix, key))
    && startKey == ApplyPrefixSet(pset, key)
  ensures var (s', io, sr) := res;
    && s'.Ready?
    && s'.cache == s.cache
  decreases counter, 1
  {
    if ref in s.cache then (
      var node := s.cache[ref];
      if BoundedKey(node.pivotTable, key) then (
        var (s0, io', pr) := getPathInternal(s, io, key, acc, tt, start, upTo, pset, maxToFind, ref, counter, node);
        var s' := s0;
        // LruModel.LruUse(s0.lru, ref);
        // var s' := s0.(lru := LruModel.Use(s0.lru, ref));
        // assert WFBCVars(s');
        (s', io', pr)
      ) else (
        (s, io, None)
      )
    ) else (
      if s.totalCacheSize() <= MaxCacheSize() - 1 then (
        var (s', io') := PageInNodeReq(s, io, ref);
        (s', io', None)
      ) else (
        (s, io, None)
      )
    )
  }

  // function {:opaque} doSucc(s: BBC.Variables, io: IO, start: UI.RangeStart, maxToFind: int)
  // : (res : (BBC.Variables, IO, Option<UI.SuccResultList>))
  // requires BBC.Inv(s)
  // requires io.IOInit?
  // requires s.Ready?
  // requires maxToFind >= 1
  // {
  //   var startKey := if start.NegativeInf? then [] else start.key;
  //   getPath(s, io, startKey, [], [], start, None, None, maxToFind, BT.G.Root(), 40)
  // }

  predicate LookupBucketsProps(lookup: BT.Lookup, buckets: seq<Bucket>, tt: TranslationTable, upTo: Option<Key>, startKey: Key)
  {
    && BT.WFLookupForKey(lookup, startKey)
    && BT.ValidTranslationTable(lookup, tt, 0)
    && upTo == BT.LookupUpperBound(lookup, tt)
    && tt == BT.LookupTranslationTable(lookup, 0, None)
    && Last(lookup).readOp.node.children.None?
    && |lookup| == |buckets|
    && (forall i | 0 <= i < |lookup| :: BoundedKey(lookup[i].readOp.node.pivotTable, lookup[i].currentKey))
    && (forall i | 0 <= i < |lookup| :: buckets[i] == lookup[i].readOp.node.buckets[Route(lookup[i].readOp.node.pivotTable, lookup[i].currentKey)])
  }

  lemma SatisfiesSuccBetreeStep(s: BBC.Variables, io: IO, start: UI.RangeStart, res: UI.SuccResultList,
    buckets: seq<Bucket>, tt: TranslationTable, lookup: BT.Lookup, maxToFind: int, startKey: Key, upTo: Option<Key>)
  requires BBC.Inv(s) && s.Ready?
  requires io.IOInit?
  requires maxToFind >= 1
  requires LookupBucketsProps(lookup, buckets, tt, upTo, startKey);
  requires forall i | 0 <= i < |lookup| :: lookup[i].readOp.ref in s.ephemeralIndirectionTable.graph
  requires forall i | 0 <= i < |lookup| :: MapsTo(s.cache, lookup[i].readOp.ref, lookup[i].readOp.node)
  requires (upTo.Some? ==> lt(startKey, upTo.value))
  requires startKey == (if start.NegativeInf? then [] else start.key)
  requires res == 
     BucketSuccessorLoopModel.GetSuccessorInBucketStack(buckets, tt, maxToFind, start, upTo);
  ensures ValidDiskOp(diskOp(io))
  ensures BBC.Next(s, s,
      IDiskOp(diskOp(io)).bdop,
      AdvanceOp(UI.SuccOp(start, res.results, res.end), false));
  {
    if (BucketListWellMarshalled(buckets)) {
      BucketSuccessorLoopModel.GetSuccessorInBucketStackResult(buckets, tt, maxToFind, start, upTo);
      assert BT.TranslateSuccBuckets(buckets, tt, 0) == BucketSuccessorLoopModel.BGM.SuccBucketList(buckets, tt);
    }

    var succStep := BT.SuccQuery(start, res.results, res.end, buckets, tt, lookup);
    assert BT.ValidSuccQuery(succStep);
    var step := BT.BetreeSuccQuery(succStep);

    assert BBC.BetreeMove(s, s,
      IDiskOp(diskOp(io)).bdop,
      AdvanceOp(UI.SuccOp(start, res.results, res.end), false),
      step);
    assert stepsBetree(s, s,
      AdvanceOp(UI.SuccOp(start, res.results, res.end), false),
      step);
  }

  function TT_NextPrefixSet(lookup: BT.Lookup, tt: TranslationTable): (pset: Option<PrefixSet>)
  requires |lookup| > 0
  requires BT.LookupTranslationTable.requires(lookup, 0, None)
  requires tt == BT.LookupTranslationTable(lookup, 0, None)
  {
    var node := Last(lookup).readOp.node;
    var curr := Translate(node.pivotTable, node.edgeTable, Last(lookup).currentKey);
    var prev := if |tt| == 0 then None else Last(tt);

    assert curr.Some? ==> IsPrefix(curr.value.prefix, Last(lookup).currentKey);
    assert prev.Some? ==> IsPrefix(prev.value.prefix, Last(lookup).currentKey);
    ComposePrefixSet(prev, curr)
  }

  lemma TranslationTableEquivIter(lookup: BT.Lookup, tt: TranslationTable, idx: int, prev: Option<PrefixSet>)
  requires 0 <= idx < |tt|
  requires |lookup| > 2 && |tt| > 1
  requires |tt| + 1  == |lookup|
  requires idx == 0 ==> prev.None?
  requires idx > 0 ==> prev == tt[idx-1]
  requires BT.LookupVisitsWFNodes(lookup)
  requires BT.LookupBoundedKey(lookup)
  requires BT.LookupFollowsChildEdges(lookup)
  requires BT.LookupFollowsChildEdges(lookup[..|lookup|-1])
  requires prev.Some? ==> IsPrefix(prev.value.prefix, lookup[idx].currentKey)
  requires lookup[0].currentKey == ApplyPrefixSet(prev, lookup[idx].currentKey)
  requires tt[..|tt|-1] == BT.LookupTranslationTable(lookup[..|lookup|-1], 0, None)
  requires tt[|tt|-1] == TT_NextPrefixSet(lookup[..|lookup|-1], tt[..|tt|-1])
  requires tt[idx..|tt|-1] == BT.LookupTranslationTable(lookup[..|lookup|-1], idx, prev)
  decreases |lookup| - idx
  ensures tt[idx..] == BT.LookupTranslationTable(lookup, idx, prev)
  {
    var tt' := BT.LookupTranslationTable(lookup, idx, prev);

    if idx == |lookup|-2 {
      assert tt' == [ TT_NextPrefixSet(lookup[..|lookup|-1], tt[..|tt|-1]) ] by {
       BT.reveal_LookupTranslationTable();
      }
    } else {
      assert idx < |lookup|-2;
      assert 0 <= idx+1 < |tt|;
  
      assert tt[idx] == tt[..|tt|-1][idx];
      assert lookup[idx+1] == lookup[..|lookup|-1][idx+1];      

      assert tt[idx].Some? ==> IsPrefix(tt[idx].value.prefix, lookup[idx+1].currentKey);
      assert lookup[0].currentKey == ApplyPrefixSet(tt[idx], lookup[idx+1].currentKey);

      TranslationTableEquivIter(lookup, tt, idx+1, tt[idx]);
      assert tt[idx+1..] == BT.LookupTranslationTable(lookup, idx+1, tt[idx]);

      assert lookup[idx] == lookup[..|lookup|-1][idx];
      assert idx == 0 ==> prev.None?;
      assert idx > 0 ==> (tt[idx-1] == tt[..|tt|-1][idx-1]);

      assert tt'[0] == tt[idx] by { BT.reveal_LookupTranslationTable(); }
      assert tt[idx..] == tt';
    }
  }

  lemma TranslationTableEquiv(lookup: BT.Lookup, tt: TranslationTable)
  requires |lookup| > 1 && |tt| > 0
  requires BT.LookupVisitsWFNodes(lookup)
  requires BT.LookupBoundedKey(lookup)
  requires BT.LookupFollowsChildEdges(lookup)
  requires BT.LookupFollowsChildEdges(lookup[..|lookup|-1])
  requires tt[..|tt|-1] == BT.LookupTranslationTable(lookup[..|lookup|-1], 0, None)
  requires tt[|tt|-1] == TT_NextPrefixSet(lookup[..|lookup|-1], tt[..|tt|-1])
  ensures tt == BT.LookupTranslationTable(lookup, 0, None)
  {
    BT.reveal_LookupTranslationTable();
    if |lookup| == 2 {
    } else {
      TranslationTableEquivIter(lookup, tt, 0, None);
    }
  }

  lemma {:timeLimitMultiplier 8} lemmaGetPathResult(s: BBC.Variables, io: IO, startKey: Key, key: Key, acc: seq<Bucket>, tt: TranslationTable,
    lookup: BT.Lookup, start: UI.RangeStart, upTo: Option<Key>, pset: Option<PrefixSet>, maxToFind: int, ref: BT.G.Reference, counter: uint64)
  requires BBC.Inv(s) && s.Ready?
  requires io.IOInit?
  requires maxToFind >= 1
  requires forall i | 0 <= i < |acc| :: WFBucket(acc[i])
  requires ref in s.ephemeralIndirectionTable.graph
  requires |lookup| > 0 ==> BT.WFLookupForKey(lookup, startKey)
  requires |lookup| > 0 ==> Last(lookup).readOp.node.children.Some?
  requires |lookup| > 0 ==> tt == BT.LookupTranslationTable(lookup, 0, None)
  requires |lookup| > 0 ==> upTo == BT.LookupUpperBound(lookup, tt)
  requires |lookup| > 0 ==> key == TranslateKey(Last(lookup).readOp.node.pivotTable, Last(lookup).readOp.node.edgeTable, Last(lookup).currentKey)
  requires |lookup| > 0 ==> ref == Last(lookup).readOp.node.children.value[Route(Last(lookup).readOp.node.pivotTable, Last(lookup).currentKey)]
  requires |lookup| > 0 ==> pset == TT_NextPrefixSet(lookup, tt)

  requires |lookup| == 0 ==> ref == BT.G.Root()
  requires |lookup| == 0 ==> key == startKey
  requires |lookup| == 0 ==> |tt| == 0 && pset == None
  requires |lookup| == 0 ==> upTo.None?
  requires |lookup| == |acc|

  requires forall i | 0 <= i < |tt| :: (tt[i].Some? ==> IsPrefix(tt[i].value.newPrefix, startKey))
  requires pset.Some? ==> IsPrefix(pset.value.prefix, key)
  requires startKey == ApplyPrefixSet(pset, key)

  requires forall i | 0 <= i < |lookup| :: acc[i] == lookup[i].readOp.node.buckets[Route(lookup[i].readOp.node.pivotTable, lookup[i].currentKey)]
  requires forall i | 0 <= i < |lookup| :: lookup[i].readOp.ref in s.ephemeralIndirectionTable.graph
  requires forall i | 0 <= i < |lookup| :: lookup[i].readOp.ref in s.cache && lookup[i].readOp.node == s.cache[lookup[i].readOp.ref]
  requires upTo.Some? ==> lt(startKey, upTo.value)
  requires startKey == (if start.NegativeInf? then [] else start.key)
  decreases counter

  ensures var (s', io', res) := getPath(s, io, key, acc, tt, start, upTo, pset, maxToFind, ref, counter);
      && ValidDiskOp(diskOp(io'))
      && IDiskOp(diskOp(io')).jdop.NoDiskOp?
      && (res.Some? ==> BBC.Next(s, s',
            IDiskOp(diskOp(io')).bdop,
            AdvanceOp(UI.SuccOp(start, res.value.results, res.value.end), false)))
      && (res.None? ==>
            betree_next_dop(s, s', IDiskOp(diskOp(io')).bdop))
    /*  && IBlockCache(s1) == s
      && s1.ephemeralIndirectionTable == s.ephemeralIndirectionTable
      && (pr.Fetch? ==> pr.ref in s.ephemeralIndirectionTable.locs)
      && (pr.Fetch? ==> pr.ref !in s.cache)
      && (pr.Path? ==> (
        && LookupBucketsProps(lookup', pr.buckets, pr.upTo, startKey))
        && (forall i | 0 <= i < |lookup'| :: lookup'[i].ref in s.ephemeralIndirectionTable.I().graph)
        && (forall i | 0 <= i < |lookup'| :: MapsTo(ICache(s.cache), lookup'[i].ref, lookup'[i].node))
        && (pr.upTo.Some? ==> lt(startKey, pr.upTo.value))
      ) */
  {
    if ref in s.cache {
      var node := s.cache[ref];
      if BoundedKey(node.pivotTable, key) {
        // reveal_getPathInternal();

        var r := Route(node.pivotTable, key);
        var bucket := node.buckets[r];
        var acc' := acc + [bucket];
        var tt' := if |acc| == 0 then tt else tt + [pset];

        var lookup' := lookup + [ BT.Layer(BT.G.ReadOp(ref, node), key) ];

        forall idx | BT.ValidLayerIndex(lookup', idx) && idx < |lookup'| - 1
        ensures BT.LookupFollowsChildRefAtLayer(lookup', idx)
        ensures BT.LookupFollowsChildEdgeAtLayer(lookup', idx)
        {
          if idx == |lookup'| - 2 {
            assert BT.LookupFollowsChildRefAtLayer(lookup', idx);
            assert BT.LookupFollowsChildEdgeAtLayer(lookup', idx);
          } else {
            assert BT.LookupFollowsChildRefAtLayer(lookup, idx);
            assert BT.LookupFollowsChildRefAtLayer(lookup', idx);
            assert BT.LookupFollowsChildEdgeAtLayer(lookup, idx);
            assert BT.LookupFollowsChildEdgeAtLayer(lookup', idx);
          }
        }

        if |lookup'| == 1 {
          assert tt' == BT.LookupTranslationTable(lookup', 0, None) by {
            BT.reveal_LookupTranslationTable();
          }
        } else {
          assert tt == BT.LookupTranslationTable(lookup, 0, None);
          TranslationTableEquiv(lookup', tt');
          assert tt' == BT.LookupTranslationTable(lookup', 0, None);
        }

        var upper := 
          if pset.None? then (
              node.pivotTable[r+1]
          ) else (
            var (left, right) := TranslatePivotPairInternal(KeyToElement(key), node.pivotTable[r+1], pset.value.prefix, pset.value.newPrefix);
            right
          );

        var upTo' := 
          if upper.Max_Element? then upTo 
          else (
            var ub : Key := upper.e;
            if upTo.None? then (
              Some(ub)
            ) else (
              var k: Key := if lt(upTo.value, upper.e) then upTo.value else ub;
              Some(k)
            ));

        assert upTo'.Some? ==> lt(startKey, upTo'.value);
        assert tt' == BT.LookupTranslationTable(lookup', 0, None);
        assert upTo' == BT.LookupUpperBound(lookup', tt') 
          by { BT.reveal_LookupUpperBound(); }

        if node.children.Some? {
          if counter == 0 {
            assert noop(s, s);
          } else {
            lemmaChildInGraph(s, ref, node.children.value[r]);
            var key' := TranslateKey(node.pivotTable, node.edgeTable, key);
            var pset' := NextPrefixSet(node.pivotTable, node.edgeTable, key, pset);
            lemmaGetPathResult(s, io, startKey, key', acc', tt', lookup', start, upTo', pset', maxToFind, node.children.value[r], counter - 1);
          }
        } else {
          var res :=
            BucketSuccessorLoopModel.GetSuccessorInBucketStack(acc', tt', maxToFind, start, upTo');
          SatisfiesSuccBetreeStep(s, io, start, res, acc', tt', lookup', maxToFind, startKey, upTo');
        }
      } else {
        assert noop(s, s);
      }
    } else {
      if s.totalCacheSize() <= MaxCacheSize() - 1 {
        assert ref in s.ephemeralIndirectionTable.graph;
        assert ref in s.ephemeralIndirectionTable.locs;
        PageInNodeReqCorrect(s, io, ref);
      } else {
        assert noop(s, s);
      }
    }
    reveal_getPath();
  }

/*
  lemma doSuccCorrect(s: BBC.Variables, io: IO, start: UI.RangeStart, maxToFind: int)
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
    BT.reveal_LookupUpperBound();
    var startKey := if start.NegativeInf? then [] else start.key;
    lemmaGetPathResult(s, io, startKey, [], [], start, None, maxToFind, BT.G.Root(), 40);
  }
  */
}
