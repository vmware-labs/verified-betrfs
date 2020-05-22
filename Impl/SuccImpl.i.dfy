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
  import opened NodeImpl
  import BucketSuccessorLoopImpl
  import BucketSuccessorLoopModel
  import opened DiskOpImpl
  import opened MainDiskIOHandler

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

  method getPathInternal(
      k: ImplConstants,
      s: ImplVariables,
      io: DiskIOHandler,
      key: Key,
      acc: seq<MutBucket>,
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
  requires forall i | 0 <= i < |acc| :: acc[i].Inv()
  requires io !in s.Repr()
  modifies s.Repr()
  modifies io
  decreases counter, 0
  ensures WellUpdated(s)
  ensures (s.I(), IIO(io), res)
       == SuccModel.getPathInternal(Ic(k), old(s.I()), old(IIO(io)), key, old(MutBucket.ISeq(acc)), start, upTo, maxToFind as int, ref, counter, old(node.I()))
  {
    SuccModel.reveal_getPathInternal();

    var r := Pivots.ComputeRoute(node.pivotTable, key);
    var bucket := node.buckets[r];
    var acc' := acc + [bucket];

    assert bucket.I() == node.I().buckets[r];

    //ghost var now_s := s.I();
    //ghost var now_acc' := MutBucket.ISeq(acc');
    //ghost var now_bucket := bucket.I();

    assert MutBucket.ISeq(acc')
        == MutBucket.ISeq(acc) + [bucket.I()];
        //== old(MutBucket.ISeq(acc)) + [bucket.I()]
        //== old(MutBucket.ISeq(acc)) + [now_bucket];

    var upTo';
    if r == |node.pivotTable| as uint64 {
      upTo' := upTo;
    } else {
      var ub := node.pivotTable[r];
      if upTo.Some? {
        var c := cmp(upTo.value, ub);
        var k: Key := if c < 0 then upTo.value else ub;
        upTo' := Some(k);
      } else {
        upTo' := Some(ub);
      }
    }

    assert MutBucket.ISeq(acc')
        == old(MutBucket.ISeq(acc) + [node.I().buckets[r]]);

    assert MutBucket.ISeq(acc')
        == old(MutBucket.ISeq(acc)) + [old(node.I()).buckets[r]];

    if node.children.Some? {
      if counter == 0 {
        print "getPathInternal failure: count ran down\n";
        res := None;

        assert (s.I(), IIO(io), res)
         == SuccModel.getPathInternal(Ic(k), old(s.I()), old(IIO(io)), key, old(MutBucket.ISeq(acc)), start, upTo, maxToFind as int, ref, counter, old(node.I()));
      } else {
        BookkeepingModel.lemmaChildInGraph(Ic(k), s.I(), ref, node.I().children.value[r]);
        res := getPath(k, s, io, key, acc', start, upTo', maxToFind, node.children.value[r], counter - 1);

        assert (s.I(), IIO(io), res)
         == SuccModel.getPathInternal(Ic(k), old(s.I()), old(IIO(io)), key, old(MutBucket.ISeq(acc)), start, upTo, maxToFind as int, ref, counter, old(node.I()));
      }
    } else {
      //assert old(MutBucket.ISeq(acc)) == MutBucket.ISeq(acc);

      MutBucket.AllocatedReprSeq(acc');

      //assert BucketSuccessorLoopModel.GetSuccessorInBucketStack(MutBucket.ISeq(acc'), maxToFind as int, start, upTo')
      //    == BucketSuccessorLoopModel.GetSuccessorInBucketStack(old(MutBucket.ISeq(acc)) + [old(node.I()).buckets[r]], maxToFind as int, start, upTo');

      var res0 := BucketSuccessorLoopImpl.GetSuccessorInBucketStack(acc', maxToFind, start, upTo');
      res := Some(res0);

      //assert res0
      //    == BucketSuccessorLoopModel.GetSuccessorInBucketStack(old(MutBucket.ISeq(acc)) + [old(node.I()).buckets[r]], maxToFind as int, start, upTo');

      //assert SuccModel.getPathInternal(Ic(k), old(s.I()), old(IIO(io)), key, old(MutBucket.ISeq(acc)), start, upTo, maxToFind as int, ref, counter, old(node.I())).2
      //    == Some(BucketSuccessorLoopModel.GetSuccessorInBucketStack(old(MutBucket.ISeq(acc)) + [old(node.I()).buckets[r]], maxToFind as int, start, upTo'))
      //    == res;

      assert (s.I(), IIO(io), res)
       == SuccModel.getPathInternal(Ic(k), old(s.I()), old(IIO(io)), key, old(MutBucket.ISeq(acc)), start, upTo, maxToFind as int, ref, counter, old(node.I()));
    }
  }

  method getPath(
      k: ImplConstants,
      s: ImplVariables,
      io: DiskIOHandler,
      key: Key,
      acc: seq<MutBucket>,
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
  requires forall i | 0 <= i < |acc| :: acc[i].Inv()
  requires io !in s.Repr()
  requires |acc| + counter as int < 0x1_0000_0000_0000_0000 - 1
  modifies s.Repr()
  modifies io
  decreases counter, 1
  ensures WellUpdated(s)
  ensures (s.I(), IIO(io), res)
       == SuccModel.getPath(Ic(k), old(s.I()), old(IIO(io)), key, old(MutBucket.ISeq(acc)), start, upTo, maxToFind as int, ref, counter)
  {
    SuccModel.reveal_getPath();

    MutBucket.AllocatedReprSeq(acc);

    var nodeOpt := s.cache.GetOpt(ref);
    if nodeOpt.Some? {
      var node := nodeOpt.value;

      assert node.I() == s.I().cache[ref];

      res := getPathInternal(k, s, io, key, acc, start, upTo, maxToFind, ref, counter, node);

      LruModel.LruUse(s.I().lru, ref);
      s.lru.Use(ref);
    } else {
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
    res := getPath(k, s, io, startKey, [], start, None, maxToFind, BT.G.Root(), 40);
  }
}
