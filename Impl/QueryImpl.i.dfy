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
  import opened ValueType
  import ValueMessage

  import opened Bounds
  import opened BucketsLib
  import PivotsLib

  import opened PBS = PivotBetreeSpec`Spec

  // == query ==

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
    QueryModel.reveal_queryIterate();

    var ref := BT.G.Root();
    var msg := ValueMessage.IdentityMessage();
    var counter: uint64 := 40;

    // TODO write this in recursive style, it would be a lot simpler?
    while true
    invariant Inv(k, s)
    invariant s.ready
    invariant ref in SM.IIndirectionTable(IIndirectionTable(s.ephemeralIndirectionTable)).graph
    invariant io.initialized()
    invariant forall s', r, io' ::
        QueryModel.queryIterate(Ic(k), s.I(), key, msg, ref, IIO(io), counter, s', r, io') ==>
        QueryModel.query(Ic(k), old(s.I()), old(IIO(io)), key, s', r, io')
    invariant counter as int >= 0
    invariant io !in s.Repr()
    invariant WellUpdated(s)
    decreases counter as int
    {
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
        MutBucket.reveal_ReprSeq();

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
            counter := counter - 1;
            ref := node.children.value[r];
          } else {
            res := Some(ValueType.DefaultValue());
            return;
          }
        }
      }
    }
  }
}
