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
  import opened StateBCImpl
  import opened StateSectorImpl
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
  import opened LinearSequence_s
  import opened LinearSequence_i

  import opened Bounds
  import opened BucketsLib
  import opened BoundedPivotsLib

  import opened PBS = PivotBetreeSpec`Spec

  // == query ==

  method queryIterate(
    
    s: ImplVariables,
    key: Key,
    msg: Message,
    ref: BT.G.Reference,
    io: DiskIOHandler,
    counter: uint64)
  returns (res: Option<Value>)
  requires io.initialized()
  requires Inv(s)
  requires io !in s.Repr()
  requires s.ready
  requires ref in s.ephemeralIndirectionTable.I().graph
  modifies io
  modifies s.Repr()
  decreases counter
  ensures WellUpdated(s)
  ensures QueryModel.queryIterate(old(s.I()), key, msg, ref, old(IIO(io)), counter, s.I(), res, IIO(io))
  {
    QueryModel.reveal_queryIterate();

    if counter == 0 {
      res := None;
      return;
    }

    var nodeOpt := s.cache.GetOpt(ref);
    if (nodeOpt.None?) {
      PageInNodeReqOrMakeRoom(s, io, ref);
      res := None;
      return;
    } else {
      var node := nodeOpt.value;
      var pivots := node.GetPivots();
      var boundedkey := ComputeBoundedKey(pivots, key);
      if !boundedkey {
        res := None;
        return;
      }

      s.cache.LemmaNodeReprLeRepr(ref);
      ghost var oldIVars := s.I();
      LruModel.LruUse(s.lru.Queue, ref);
      s.lru.Use(ref);
      assert SBCM.IBlockCache(oldIVars) == SBCM.IBlockCache(s.I());

      var r := Pivots.ComputeRoute(pivots, key);

      var kmtMsg := lseq_peek(node.box.Borrow().buckets, r).Query(key);
      var newmsg := if kmtMsg.Some? then ValueMessage.Merge(msg, kmtMsg.value) else msg;

      if (newmsg.Define?) {
        res := Some(newmsg.value);
        return;
      } else {
        var children := node.GetChildren();
        if children.Some? {
          BookkeepingModel.lemmaChildInGraph(s.I(), ref, children.value[r]);
          res := queryIterate(s, key, newmsg, children.value[r], io, counter - 1);
        } else {
          res := Some(ValueType.DefaultValue());
          return;
        }
      }
    }
  }

  method query(s: ImplVariables, io: DiskIOHandler, key: Key)
  returns (res: Option<Value>)
  requires io.initialized()
  requires Inv(s)
  requires io !in s.Repr()
  requires s.ready
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures QueryModel.query(old(s.I()), old(IIO(io)), key, s.I(), res, IIO(io))
  {
    QueryModel.reveal_query();

    var ref := BT.G.Root();
    var msg := ValueMessage.IdentityMessage();
    var counter: uint64 := 40;

    res := queryIterate(s, key, msg, ref, io, counter);
  }
}
