// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "BookkeepingImpl.i.dfy"
include "SuccModel.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sets.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "BucketSuccessorLoopImpl.i.dfy"

// See dependency graph in MainHandlers.dfy

module SuccImpl { 
  import opened IOImpl
  import SuccModel
  import BookkeepingModel
  import opened StateBCImpl
  import opened Lexicographic_Byte_Order_Impl
  import opened NodeImpl
  import CacheImpl

  import BGI = BucketGeneratorImpl
  import BGM = BucketGeneratorModel
  import BucketSuccessorLoopImpl
  import BucketSuccessorLoopModel
  import opened DiskOpImpl
  import opened MainDiskIOHandler

  import opened LinearOption
  import opened LinearSequence_s
  import opened LinearSequence_i
  import opened Options
  import opened NativeTypes
  import opened Maps
  import opened Sets
  import opened Sequences
  import opened KeyType

  import opened Bounds
  import opened BucketsLib
  import opened BoundedPivotsLib
  import opened TranslationLib
  import opened TranslationImpl

  import opened InterpretationDiskOps
  import opened ViewOp
  import opened DiskOpModel

  predicate TranslationTableInv(acc: seq<Bucket>, tt: TranslationTable, key: Key, pset: Option<PrefixSet>, start: UI.RangeStart)
  {
    var startKey := if start.NegativeInf? then [] else start.key;
    && (|acc| == 0 ==> |tt| == 0 && pset == None)
    && (|acc| > 0 ==> |tt| + 1 == |acc|)
    && (pset.Some? ==> IsPrefix(pset.value.prefix, key))
    && ApplyPrefixSet(pset, key) == startKey
    && (forall i | 0 <= i < |tt| :: (tt[i].Some? ==> IsPrefix(tt[i].value.newPrefix, startKey)))
  }

  method composeGenerator(shared cache: CacheImpl.LMutCache, ref: BT.G.Reference, r: uint64,
    linear g: lOption<BGI.Generator>, pset: Option<PrefixSet>, start: UI.RangeStart, key: Key,
    ghost tt: TranslationTable, ghost acc: seq<Bucket>, ghost bucket: Bucket)
  returns (linear g': BGI.Generator)
  requires cache.Inv()
  requires cache.ptr(ref).Some?
  requires BT.WFNode(cache.I()[ref])
  requires r as nat < |cache.I()[ref].buckets|
  requires bucket == cache.I()[ref].buckets[r as nat]
  requires WFBucket(bucket)
  requires forall i | 0 <= i < |acc| :: WFBucket(acc[i])
  requires TranslationTableInv(acc, tt, key, pset, start)
  requires g.lSome? <==> |acc| >= 1
  requires g.lSome? ==> g.value.Inv() && g.value.I()
    == BGM.GenFromBucketStackWithLowerBound(acc, start, tt)
  ensures g'.Inv()
  ensures var tt' := if |acc| == 0 then tt else tt + [pset];
    && g'.I() == BGM.GenFromBucketStackWithLowerBound(acc + [bucket], start, tt')
  {
    linear var g2 := cache.NodeBucketGen(ref, r, start, key, pset);
    BGM.reveal_GenFromBucketStackWithLowerBound();
    linear match g {
      case lSome(g1) =>
        g' := BGI.Generator.GenCompose(g1, g2);
      case lNone() => 
        g' := g2;
    }
  }

  method {:timeLimitMultiplier 4} getPathInternal(
      linear inout s: ImplVariables,
      io: DiskIOHandler,
      key: Key,
      ghost acc: seq<Bucket>,
      ghost tt: TranslationTable,
      linear g: lOption<BGI.Generator>,
      start: UI.RangeStart,
      upTo: Option<Key>,
      pset: Option<PrefixSet>,
      maxToFind: uint64,
      ref: BT.G.Reference,
      counter: uint64,
      pivots: PivotTable,
      edges: EdgeTable,
      children: Option<seq<BT.G.Reference>>)
  returns (res : Option<UI.SuccResultList>)
  requires old_s.Ready? && old_s.Inv()
  requires io.initialized()
  requires old_s.cache.ptr(ref).Some?
  requires BT.WFNode(old_s.cache.I()[ref])
  requires pivots == old_s.cache.I()[ref].pivotTable
  requires edges == old_s.cache.I()[ref].edgeTable
  requires children == old_s.cache.I()[ref].children
  requires BoundedKey(pivots, key)
  requires ref in old_s.ephemeralIndirectionTable.graph
  requires maxToFind >= 1
  requires |acc| + counter as int < 0x1_0000_0000_0000_0000 - 1
  requires forall i | 0 <= i < |acc| :: WFBucket(acc[i])
  requires TranslationTableInv(acc, tt, key, pset, start)
  requires g.lSome? <==> |acc| >= 1
  requires g.lSome? ==> g.value.Inv() && g.value.I()
    == BGM.GenFromBucketStackWithLowerBound(acc, start, tt)
  modifies io
  decreases counter, 0
  ensures s.WFBCVars()
  ensures s.Ready?
  ensures s.cache.I() == old_s.cache.I()
  ensures (s.I(), IIO(io), res)
       == SuccModel.getPathInternal(old_s.I(), old(IIO(io)), key, old(acc), old(tt),
      start, upTo, pset, maxToFind as int, ref, counter, s.cache.I()[ref])
  {
    SuccModel.reveal_getPathInternal();
    
    var r := Pivots.ComputeRoute(pivots, key);
    ghost var node := s.cache.I()[ref];
    ghost var bucket := s.cache.I()[ref].buckets[r as nat];
    ghost var acc' := acc + [bucket];
    ghost var tt' := if |acc| == 0 then tt else tt + [pset];

    var upper;
    if pset.None? {
      upper := pivots[r+1];
    } else {
      var _, right := ComputeTranslatePivotPair(key, pivots[r+1], pset.value.prefix, pset.value.newPrefix);
      upper := right;
    }

    var upTo';
    if upper.Max_Element? {
      upTo' := upTo;
    } else {
      var ub : Key := upper.e;
      if upTo.Some? {
        var c := cmp(upTo.value, ub);
        var k: Key := if c < 0 then upTo.value else ub;
        upTo' := Some(k);
      } else {
        upTo' := Some(ub);
      }
    }

    if children.Some? {
      if counter == 0 {
        print "getPathInternal failure: count ran down\n";
        res := None;
        linear match g {
          case lSome(g1) =>
            g1.Free();
          case lNone() =>
        }

        assert (s.I(), IIO(io), res)
         == SuccModel.getPathInternal(old_s.I(), old(IIO(io)), key, old(acc), old(tt),
          start, upTo, pset, maxToFind as int, ref, counter, node);
      } else {
        var key', pset';

        if edges[r].None? {
          key' := key;
          pset' := pset;
        } else {
          var translate := ComputeTranslatePrefixSet(pivots, edges, key, r);
          assert edges[r].Some? <==> translate.Some?;

          key' := ApplyPrefixSet(translate, key);

          assert translate.Some? ==> IsPrefix(translate.value.prefix, key);
          assert pset.Some? ==> IsPrefix(pset.value.prefix, key);
          pset' := ComputeComposePrefixSet(pset, translate);
          assert pset'.Some? ==> IsPrefix(pset'.value.prefix, key');

          ghost var startKey := if start.NegativeInf? then [] else start.key;
          ComposePrefixSetCorrect(pset, translate, pset', startKey, key, key');
        }

        BookkeepingModel.lemmaChildInGraph(s.I(), ref, children.value[r]);
        linear var g' := composeGenerator(s.cache, ref, r, g, pset, start, key, tt, acc, bucket);

        res := getPath(inout s, io, key', acc', tt', lSome(g'), start, upTo', pset',
            maxToFind, children.value[r], counter - 1);

        assert (s.I(), IIO(io), res)
         == SuccModel.getPathInternal(old_s.I(), old(IIO(io)), key, old(acc), old(tt),
          start, upTo, pset, maxToFind as int, ref, counter, node);
      }
    } else {
      linear var g' := composeGenerator(s.cache, ref, r, g, pset, start, key, tt, acc, bucket);
      var res0 := BucketSuccessorLoopImpl.GetSuccessorInBucketStack(g', acc', tt', maxToFind, start, upTo');
      res := Some(res0);

      assert (s.I(), IIO(io), res)
       == SuccModel.getPathInternal(old_s.I(), old(IIO(io)), key,
        old(acc), old(tt), start, upTo, pset, maxToFind as int, ref, counter, node);
    }
  }

  method {:timeLimitMultiplier 2} getPath(
      linear inout s: ImplVariables,
      io: DiskIOHandler,
      key: Key,
      ghost acc: seq<Bucket>,
      ghost tt: TranslationTable,
      linear g: lOption<BGI.Generator>,
      start: UI.RangeStart,
      upTo: Option<Key>,
      pset: Option<PrefixSet>,
      maxToFind: uint64,
      ref: BT.G.Reference,
      counter: uint64)
  returns (res : Option<UI.SuccResultList>)
  requires old_s.Inv() && old_s.Ready?
  requires io.initialized()
  requires maxToFind >= 1
  requires ref in old_s.ephemeralIndirectionTable.graph
  requires forall i | 0 <= i < |acc| :: WFBucket(acc[i])
  requires TranslationTableInv(acc, tt, key, pset, start)
  requires |acc| + counter as int < 0x1_0000_0000_0000_0000 - 1
  requires g.lSome? <==> |acc| >= 1
  requires g.lSome? ==> g.value.Inv() && g.value.I()
    == BGM.GenFromBucketStackWithLowerBound(acc, start, tt)
  modifies io
  decreases counter, 1
  ensures s.WFBCVars()
  ensures (s.I(), IIO(io), res)
       == SuccModel.getPath(old_s.I(), old(IIO(io)), key, old(acc), old(tt), start,
        upTo, pset, maxToFind as int, ref, counter)
  {
    SuccModel.reveal_getPath();

    var incache := s.cache.InCache(ref);
    if incache {
      var pivots, edges, children := s.cache.GetNodeInfo(ref);
      var boundedkey := ComputeBoundedKey(pivots, key);
      if boundedkey {
        res := getPathInternal(inout s, io, key, acc, tt, g, start, upTo,
          pset, maxToFind, ref, counter, pivots, edges, children);
        LruModel.LruUse(s.lru.Queue(), ref);
        inout s.lru.Use(ref);
      } else {
        linear match g {
          case lSome(g1) =>
            g1.Free();
          case lNone() =>
        }
        print "getPath: look up key is not bounded in path nodes\n";
        res := None;
      }
    } else {
      linear match g {
        case lSome(g1) =>
          g1.Free();
        case lNone() =>
      }
      // TODO factor this out into something that checks (and if it's full, actually
      // does something).
      if CacheImpl.CacheCount(s.cache) + |s.outstandingBlockReads| as uint64 <= MaxCacheSizeUint64() - 1 {
        PageInNodeReq(inout s, io, ref);
      } else {
        print "getPath: Can't page in anything because cache is full\n";
      }
      res := None;
    }
  }

  method doSucc(linear inout s: ImplVariables, io: DiskIOHandler, start: UI.RangeStart, maxToFind: uint64)
  returns (res : Option<UI.SuccResultList>)
  requires old_s.Inv() && old_s.Ready?
  requires io.initialized()
  requires maxToFind >= 1
  modifies io
  ensures s.WFBCVars()
  ensures ValidDiskOp(diskOp(IIO(io)))
    && IDiskOp(diskOp(IIO(io))).jdop.NoDiskOp?
    && (res.Some? ==>
            BBC.Next(old_s.I(), s.I(), IDiskOp(diskOp(IIO(io))).bdop,
            AdvanceOp(UI.SuccOp(start, res.value.results, res.value.end), false)))
    && (res.None? ==>
            IOModel.betree_next_dop(old_s.I(), s.I(), IDiskOp(diskOp(IIO(io))).bdop))
  {
    BT.reveal_LookupUpperBound();
    var startKey := if start.NegativeInf? then [] else start.key;
    SuccModel.lemmaGetPathResult(old_s.I(), IIO(io), startKey, startKey, 
      [], [], [], start, None, None, maxToFind as int, BT.G.Root(), 40);
    res := getPath(inout s, io, startKey, [], [], lNone, start, None, None, maxToFind, BT.G.Root(), 40);
  }
}