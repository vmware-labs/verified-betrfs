include "SyncImpl.i.dfy"
include "SuccModel.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sets.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "BucketSuccessorLoopImpl.i.dfy"

// See dependency graph in MainHandlers.dfy

module SuccImpl { 
  import opened SyncImpl
  import opened IOImpl
  import SuccModel
  import BookkeepingModel
  import opened StateBCImpl
  import opened BucketImpl
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

  method composeGenerator(cache: CacheImpl.MutCache, ref: BT.G.Reference, r: uint64, 
    linear g: lOption<BGI.Generator>, ghost acc: seq<Bucket>, ghost bucket: Bucket,
    start: UI.RangeStart)
  returns (linear g': BGI.Generator)
  requires cache.Inv()
  requires cache.ptr(ref).Some?
  requires SSM.WFNode(cache.I()[ref])
  requires r as nat < |cache.I()[ref].buckets|
  requires bucket == cache.I()[ref].buckets[r as nat]
  requires WFBucket(bucket)
  requires forall i | 0 <= i < |acc| :: WFBucket(acc[i])
  requires g.lSome? <==> |acc| >= 1
  requires g.lSome? ==> g.value.Inv() && g.value.I()
    == BGM.GenFromBucketStackWithLowerBound(acc, start)
  ensures g'.Inv() && g'.I()
    == BGM.GenFromBucketStackWithLowerBound(acc + [bucket], start)
  {
    linear var g2 := cache.NodeBucketGen(ref, r, start);
    BGM.reveal_GenFromBucketStackWithLowerBound();
    linear match g {
      case lSome(g1) =>
        g' := BGI.Generator.GenCompose(g1, g2);
      case lNone() => 
        g' := g2;
    }
  }

  method getPathInternal(
      s: ImplVariables,
      io: DiskIOHandler,
      key: Key,
      ghost acc: seq<Bucket>,
      linear g: lOption<BGI.Generator>,
      start: UI.RangeStart,
      upTo: Option<Key>,
      maxToFind: uint64,
      ref: BT.G.Reference,
      counter: uint64,
      pivots: PivotTable,
      children: Option<seq<BT.G.Reference>>)
  returns (res : Option<UI.SuccResultList>)
  requires s.ready
  requires Inv(s)
  requires io.initialized()
  requires s.cache.ptr(ref).Some?
  requires SSM.WFNode(s.cache.I()[ref])
  requires pivots == s.cache.I()[ref].pivotTable
  requires children == s.cache.I()[ref].children
  requires BoundedKey(pivots, key)
  requires ref in s.I().ephemeralIndirectionTable.graph
  requires maxToFind >= 1
  requires |acc| + counter as int < 0x1_0000_0000_0000_0000 - 1
  requires forall i | 0 <= i < |acc| :: WFBucket(acc[i])
  requires g.lSome? <==> |acc| >= 1
  requires g.lSome? ==> g.value.Inv() && g.value.I()
    == BGM.GenFromBucketStackWithLowerBound(acc, start)
  requires io !in s.Repr()
  modifies s.Repr()
  modifies io
  decreases counter, 0
  ensures WellUpdated(s)
  ensures s.cache.I() == old(s.cache.I())
  ensures (s.I(), IIO(io), res)
       == SuccModel.getPathInternal(old(s.I()), old(IIO(io)), key, old(acc),
      start, upTo, maxToFind as int, ref, counter, s.cache.I()[ref])
  {
    SuccModel.reveal_getPathInternal();

    var r := Pivots.ComputeRoute(pivots, key);
    ghost var node := s.cache.I()[ref];
    ghost var bucket := s.cache.I()[ref].buckets[r as nat];
    ghost var acc' := acc + [bucket];

    var upTo';
    if pivots[r+1].Max_Element? {
      upTo' := upTo;
    } else {
      var ub := ComputeGetKey(pivots, r+1);
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
         == SuccModel.getPathInternal(old(s.I()), old(IIO(io)), key, old(acc),
          start, upTo, maxToFind as int, ref, counter, node);
      } else {
        BookkeepingModel.lemmaChildInGraph(s.I(), ref, children.value[r]);
        linear var g' := composeGenerator(s.cache, ref, r, g, acc, bucket, start);
        res := getPath(s, io, key, acc', lSome(g'), start, upTo', maxToFind,
          children.value[r], counter - 1);
        
        assert (s.I(), IIO(io), res)
         == SuccModel.getPathInternal(old(s.I()), old(IIO(io)), key, old(acc),
          start, upTo, maxToFind as int, ref, counter, node);
      }
    } else {
      linear var g' := composeGenerator(s.cache, ref, r, g, acc, bucket, start);
      var res0 := BucketSuccessorLoopImpl.GetSuccessorInBucketStack(g', acc',
        maxToFind, start, upTo');
      res := Some(res0);

      assert (s.I(), IIO(io), res)
       == SuccModel.getPathInternal(old(s.I()), old(IIO(io)), key,
        old(acc), start, upTo, maxToFind as int, ref, counter, node);
    }
  }

  method getPath(
      s: ImplVariables,
      io: DiskIOHandler,
      key: Key,
      ghost acc: seq<Bucket>,
      linear g: lOption<BGI.Generator>,
      start: UI.RangeStart,
      upTo: Option<Key>,
      maxToFind: uint64,
      ref: BT.G.Reference,
      counter: uint64)
  returns (res : Option<UI.SuccResultList>)
  requires Inv(s)
  requires s.ready
  requires io.initialized()
  requires maxToFind >= 1
  requires ref in s.I().ephemeralIndirectionTable.graph
  requires forall i | 0 <= i < |acc| :: WFBucket(acc[i])
  requires io !in s.Repr()
  requires |acc| + counter as int < 0x1_0000_0000_0000_0000 - 1
  requires g.lSome? <==> |acc| >= 1
  requires g.lSome? ==> g.value.Inv() && g.value.I()
    == BGM.GenFromBucketStackWithLowerBound(acc, start)
  modifies s.Repr()
  modifies io
  decreases counter, 1
  ensures WellUpdated(s)
  ensures (s.I(), IIO(io), res)
       == SuccModel.getPath(old(s.I()), old(IIO(io)), key, old(acc), start,
        upTo, maxToFind as int, ref, counter)
  {
    SuccModel.reveal_getPath();

    var incache := s.cache.InCache(ref);
    if incache {
      var pivots, children := s.cache.GetNodeInfo(ref);
      var boundedkey := ComputeBoundedKey(pivots, key);
      if boundedkey {
        res := getPathInternal(s, io, key, acc, g, start, upTo,
          maxToFind, ref, counter, pivots, children);
        LruModel.LruUse(s.I().lru, ref);
        s.lru.Use(ref);
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
      if s.cache.Count() + |s.outstandingBlockReads| as uint64 <= MaxCacheSizeUint64() - 1 {
        PageInNodeReq(s, io, ref);
      } else {
        print "getPath: Can't page in anything because cache is full\n";
      }
      res := None;
    }
  }

  method doSucc(s: ImplVariables, io: DiskIOHandler, start: UI.RangeStart, maxToFind: uint64)
  returns (res : Option<UI.SuccResultList>)
  requires Inv(s)
  requires io.initialized()
  requires io !in s.Repr()
  requires maxToFind >= 1
  requires s.ready
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures (s.I(), IIO(io), res) == SuccModel.doSucc(old(s.I()), old(IIO(io)),
    start, maxToFind as int)
  {
    SuccModel.reveal_doSucc();
    var startKey := if start.NegativeInf? then [] else start.key;
    res := getPath(s, io, startKey, [], lNone, start, None, maxToFind, BT.G.Root(), 40);
  }
}
