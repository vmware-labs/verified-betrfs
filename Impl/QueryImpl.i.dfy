include "SyncImpl.i.dfy"
include "QueryModel.i.dfy"
include "EvictImpl.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sets.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"

// See dependency graph in MainHandlers.dfy

module QueryImpl { 
  import opened SyncImpl
  import opened IOImpl
  import QueryModel
  import BookkeepingModel
  import opened StateImpl
  import opened BucketImpl
  import opened EvictImpl
  import opened DiskOpImpl
  import opened MainDiskIOHandler

  import opened Options
  import opened NativeTypes
  import opened Maps
  import opened Sets
  import opened Sequences
  import opened KeyType
  import opened ValueMessage

  import opened Bounds
  import opened BucketsLib
  import PivotsLib

  import opened PBS = PivotBetreeSpec`Spec

  // == query ==

  method queryIterate(
    k: ImplConstants,
    s: ImplVariables,
    key: Key,
    msg: Message,
    ref: BT.G.Reference,
    io: DiskIOHandler,
    counter: uint64)
  returns (res: Option<Value>)
  requires io.initialized()
  requires Inv(k, s)
  requires io !in s.Repr()
  requires s.ready
  requires ref in SM.IIndirectionTable(IIndirectionTable(s.ephemeralIndirectionTable)).graph
  modifies io
  modifies s.Repr()
  decreases counter
  ensures WellUpdated(s)
  ensures QueryModel.queryIterate(Ic(k), old(s.I()), key, msg, ref, old(IIO(io)), counter, s.I(), res, IIO(io))
  {
    QueryModel.reveal_queryIterate();

    if counter == 0 {
      res := None;
      return;
    }

    var nodeOpt := s.cache.GetOpt(ref);
    if (nodeOpt.None?) {
      PageInNodeReqOrMakeRoom(k, s, io, ref);
      res := None;
      return;
    } else {
      var node := nodeOpt.value;

      node.LemmaReprSeqBucketsLeRepr();
      s.cache.LemmaNodeReprLeRepr(ref);
      //MutBucket.reveal_ReprSeq();
      MutBucket.AllocatedReprSeq(node.buckets);
      MutBucket.LemmaReprBucketLeReprSeq(node.buckets,
          Pivots.Route(node.pivotTable, key));
      //assert node.buckets[Pivots.Route(node.pivotTable, key)].Repr
      //    <= MutBucket.ReprSeq(node.buckets);

      ghost var oldIVars := s.I();
      LruModel.LruUse(s.lru.Queue, ref);
      s.lru.Use(ref);
      assert SM.IBlockCache(oldIVars) == SM.IBlockCache(s.I());

      var r := Pivots.ComputeRoute(node.pivotTable, key);
      var bucket := node.buckets[r];

      var kmtMsg := bucket.Query(key);
      var newmsg := if kmtMsg.Some? then ValueMessage.Merge(msg, kmtMsg.value) else msg;

      if (newmsg.Define?) {
        res := Some(newmsg.value);
        return;
      } else {
        if node.children.Some? {
          BookkeepingModel.lemmaChildInGraph(Ic(k), s.I(), ref, node.children.value[r]);
          res := queryIterate(k, s, key, newmsg, node.children.value[r], io, counter - 1);
        } else {
          res := Some(ValueType.DefaultValue());
          return;
        }
      }
    }
  }

  method query(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, key: Key)
  returns (res: Option<Value>)
  requires io.initialized()
  requires Inv(k, s)
  requires io !in s.Repr()
  requires s.ready
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures QueryModel.query(Ic(k), old(s.I()), old(IIO(io)), key, s.I(), res, IIO(io))
  {
    QueryModel.reveal_query();

    var ref := BT.G.Root();
    var msg := ValueMessage.IdentityMessage();
    var counter: uint64 := 40;

    res := queryIterate(k, s, key, msg, ref, io, counter);
  }
}
