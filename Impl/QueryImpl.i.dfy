// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

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
    linear inout s: ImplVariables,
    key: Key,
    msg: Message,
    ref: BT.G.Reference,
    io: DiskIOHandler,
    counter: uint64)
  returns (res: Option<Value>)
  requires io.initialized()
  requires old_s.Inv()
  requires old_s.Ready?
  requires ref in old_s.ephemeralIndirectionTable.I().graph
  modifies io
  decreases counter
  ensures s.W()
  ensures QueryModel.queryIterate(old_s.I(), key, msg, ref, old(IIO(io)), counter, s.I(), res, IIO(io))
  {
    QueryModel.reveal_queryIterate();

    if counter == 0 {
      res := None;
    } else {
      var incache := s.cache.InCache(ref);
      if !incache {
        PageInNodeReqOrMakeRoom(inout s, io, ref);
        res := None;
      } else {
        assert s.cache.I() == old(s.cache.I());
        var pivots, children := s.cache.GetNodeInfo(ref);

        var boundedkey := ComputeBoundedKey(pivots, key);
        if !boundedkey {
          res := None;
        } else {
          ghost var oldIVars := s.I();
          LruModel.LruUse(s.lru.Queue(), ref);
          inout s.lru.Use(ref);
          assert SBCM.IBlockCache(oldIVars) == SBCM.IBlockCache(s.I());

          var r := Pivots.ComputeRoute(pivots, key);
          var kmtMsg := s.cache.GetMessage(ref, r, key);
          var newmsg := if kmtMsg.Some? then ValueMessage.Merge(msg, kmtMsg.value) else msg;

          if (newmsg.Define?) {
            res := Some(newmsg.value);
          } else {
            if children.Some? {
              BookkeepingModel.lemmaChildInGraph(s.I(), ref, children.value[r]);
              res := queryIterate(inout s, key, newmsg, children.value[r], io, counter - 1);

              ghost var a := QueryModel.queryIterate(old_s.I(), key, msg, ref, 
                old(IIO(io)), counter, s.I(), res, IIO(io));
              assert a;
            } else {
              res := Some(ValueType.DefaultValue());
            }
          }
        }
      }
    }
  }

  method query(linear inout s: ImplVariables, io: DiskIOHandler, key: Key)
  returns (res: Option<Value>)
  requires io.initialized()
  requires old_s.Inv()
  requires old_s.Ready?
  modifies io
  ensures s.W()
  ensures QueryModel.query(old_s.I(), old(IIO(io)), key, s.I(), res, IIO(io))
  {
    QueryModel.reveal_query();

    var ref := BT.G.Root();
    var msg := ValueMessage.IdentityMessage();
    var counter: uint64 := 40;

    res := queryIterate(inout s, key, msg, ref, io, counter);
  }
}
