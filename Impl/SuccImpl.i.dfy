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
  import opened StateImpl
  import opened BucketImpl
  import opened Lexicographic_Byte_Order_Impl
  import opened BoxNodeImpl

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
  import PivotsLib

  import opened PBS = PivotBetreeSpec`Spec

  method composeGenerator(node: Node, r: uint64, linear g: lOption<BGI.Generator>, ghost acc: seq<Bucket>, ghost bucket: Bucket, start: UI.RangeStart) returns (linear g': BGI.Generator)
  requires node.Inv()
  requires r as nat < |node.Read().buckets|
  requires bucket == node.Read().buckets[r as nat].I()
  requires StateModel.WFNode(node.I())
  requires WFBucket(bucket)
  requires forall i | 0 <= i < |acc| :: WFBucket(acc[i])
  requires g.lSome? <==> |acc| >= 1
  requires g.lSome? ==> g.value.Inv() && g.value.I() == BGM.GenFromBucketStackWithLowerBound(acc, start)
  ensures g'.Inv() && g'.I() == BGM.GenFromBucketStackWithLowerBound(acc + [bucket], start);
  {
    linear var g2 := BGI.Generator.GenFromBucketWithLowerBound(lseq_peek(node.box.Borrow().buckets, r), start);
    BGM.reveal_GenFromBucketStackWithLowerBound();
    linear match g {
      case lSome(g1) =>
        g' := BGI.Generator.GenCompose(g1, g2);
        assert g'.Inv() && g'.I() == BGM.GenFromBucketStackWithLowerBound(acc + [bucket], start);
      case lNone() => 
        g' := g2;
        assert g'.Inv() && g'.I() == BGM.GenFromBucketStackWithLowerBound([bucket], start);
    }
  }

  method getPathInternal(
      k: ImplConstants,
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
      node: Node)
  returns (res : Option<UI.SuccResultList>)
  requires Inv(k, s)
  requires node.Inv()
  requires StateModel.WFNode(node.I())
  requires s.ready
  requires io.initialized()
  requires ref in s.I().cache
  requires ref in s.I().ephemeralIndirectionTable.graph
  requires node.I() == s.I().cache[ref]
  requires maxToFind >= 1
  requires |acc| + counter as int < 0x1_0000_0000_0000_0000 - 1
  requires forall i | 0 <= i < |acc| :: WFBucket(acc[i])
  requires g.lSome? <==> |acc| >= 1
  requires g.lSome? ==> g.value.Inv() && g.value.I() == BGM.GenFromBucketStackWithLowerBound(acc, start)
  requires io !in s.Repr()
  modifies s.Repr()
  modifies io
  decreases counter, 0
  ensures WellUpdated(s)
  ensures (s.I(), IIO(io), res)
       == SuccModel.getPathInternal(Ic(k), old(s.I()), old(IIO(io)), key, old(acc), start, upTo, maxToFind as int, ref, counter, old(node.I()))
  {
    SuccModel.reveal_getPathInternal();

    var pivots := node.GetPivots();
    var r := Pivots.ComputeRoute(pivots, key);

    ghost var bucket := node.Read().buckets[r as nat].I();
    ghost var acc' := acc + [bucket];

    var upTo';
    if r == |pivots| as uint64 {
      upTo' := upTo;
    } else {
      var ub := pivots[r];
      if upTo.Some? {
        var c := cmp(upTo.value, ub);
        var k: Key := if c < 0 then upTo.value else ub;
        upTo' := Some(k);
      } else {
        upTo' := Some(ub);
      }
    }

    var children := node.GetChildren();
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
         == SuccModel.getPathInternal(Ic(k), old(s.I()), old(IIO(io)), key, old(acc), start, upTo, maxToFind as int, ref, counter, old(node.I()));
      } else {
        BookkeepingModel.lemmaChildInGraph(Ic(k), s.I(), ref, node.I().children.value[r]);
        linear var g' := composeGenerator(node, r, g, acc, bucket, start);
        res := getPath(k, s, io, key, acc', lSome(g'), start, upTo', maxToFind, children.value[r], counter - 1);

        assert (s.I(), IIO(io), res)
         == SuccModel.getPathInternal(Ic(k), old(s.I()), old(IIO(io)), key, old(acc), start, upTo, maxToFind as int, ref, counter, old(node.I()));
      }
    } else {
      //assert old(MutBucket.ISeq(acc)) == MutBucket.ISeq(acc);

      //assert BucketSuccessorLoopModel.GetSuccessorInBucketStack(MutBucket.ISeq(acc'), maxToFind as int, start, upTo')
      //    == BucketSuccessorLoopModel.GetSuccessorInBucketStack(old(MutBucket.ISeq(acc)) + [old(node.I()).buckets[r]], maxToFind as int, start, upTo');
      // now we are ready!
      linear var g' := composeGenerator(node, r, g, acc, bucket, start);
      var res0 := BucketSuccessorLoopImpl.GetSuccessorInBucketStack(g', acc', maxToFind, start, upTo');
      res := Some(res0);

      //assert res0
      //    == BucketSuccessorLoopModel.GetSuccessorInBucketStack(old(MutBucket.ISeq(acc)) + [old(node.I()).buckets[r]], maxToFind as int, start, upTo');

      //assert SuccModel.getPathInternal(Ic(k), old(s.I()), old(IIO(io)), key, old(MutBucket.ISeq(acc)), start, upTo, maxToFind as int, ref, counter, old(node.I())).2
      //    == Some(BucketSuccessorLoopModel.GetSuccessorInBucketStack(old(MutBucket.ISeq(acc)) + [old(node.I()).buckets[r]], maxToFind as int, start, upTo'))
      //    == res;

      assert (s.I(), IIO(io), res)
       == SuccModel.getPathInternal(Ic(k), old(s.I()), old(IIO(io)), key, old(acc), start, upTo, maxToFind as int, ref, counter, old(node.I()));
    }
  }

  method getPath(
      k: ImplConstants,
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
  requires Inv(k, s)
  requires s.ready
  requires io.initialized()
  requires maxToFind >= 1
  requires ref in s.I().ephemeralIndirectionTable.graph
  requires forall i | 0 <= i < |acc| :: WFBucket(acc[i])
  requires io !in s.Repr()
  requires |acc| + counter as int < 0x1_0000_0000_0000_0000 - 1
  requires g.lSome? <==> |acc| >= 1
  requires g.lSome? ==> g.value.Inv() && g.value.I() == BGM.GenFromBucketStackWithLowerBound(acc, start)
  modifies s.Repr()
  modifies io
  decreases counter, 1
  ensures WellUpdated(s)
  ensures (s.I(), IIO(io), res)
       == SuccModel.getPath(Ic(k), old(s.I()), old(IIO(io)), key, old(acc), start, upTo, maxToFind as int, ref, counter)
  {
    SuccModel.reveal_getPath();

    var nodeOpt := s.cache.GetOpt(ref);
    if nodeOpt.Some? {
      var node := nodeOpt.value;

      assert node.I() == s.I().cache[ref];
      res := getPathInternal(k, s, io, key, acc, g, start, upTo, maxToFind, ref, counter, node);

      LruModel.LruUse(s.I().lru, ref);
      s.lru.Use(ref);
    } else {
      linear match g {
        case lSome(g1) =>
          g1.Free();
        case lNone() =>
      }
      // TODO factor this out into something that checks (and if it's full, actually
      // does something).
      if s.cache.Count() + |s.outstandingBlockReads| as uint64 <= MaxCacheSizeUint64() - 1 {
        PageInNodeReq(k, s, io, ref);
      } else {
        print "getPath: Can't page in anything because cache is full\n";
      }
      res := None;
    }
  }

  method doSucc(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, start: UI.RangeStart, maxToFind: uint64)
  returns (res : Option<UI.SuccResultList>)
  requires Inv(k, s)
  requires io.initialized()
  requires io !in s.Repr()
  requires maxToFind >= 1
  requires s.ready
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures (s.I(), IIO(io), res) == SuccModel.doSucc(Ic(k), old(s.I()), old(IIO(io)), start, maxToFind as int)
  {
    SuccModel.reveal_doSucc();
    var startKey := if start.NegativeInf? then [] else start.key;
    res := getPath(k, s, io, startKey, [], lNone, start, None, maxToFind, BT.G.Root(), 40);
  }
}
