// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

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
  import opened QueryModel
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
  import opened TranslationImpl
  import opened DiskOpModel
  import opened InterpretationDiskOps
  import opened ViewOp

  // == query ==

  method queryIterate(linear inout s: ImplVariables, querykey: Key, key: Key, msg: Message,
    ref: BT.G.Reference, io: DiskIOHandler, counter: uint64, ghost lookup: seq<BT.Layer>)
  returns (res: Option<Value>)

  requires old_s.Inv()
  requires queryInv(old_s.I(), querykey, key, msg, ref, IIO(io), counter as int, lookup)
  requires !msg.Define?
  requires io.initialized()

  modifies io
  decreases counter, 1
  ensures s.WFBCVars()

  ensures ValidDiskOp(diskOp(IIO(io)))
  ensures IDiskOp(diskOp(IIO(io))).jdop.NoDiskOp?
  ensures res.Some? ==>
      BBC.Next(old_s.I(), s.I(),
          IDiskOp(diskOp(IIO(io))).bdop,
          AdvanceOp(UI.GetOp(querykey, res.value), false));
  ensures res.None? ==>
      IOModel.betree_next_dop(old_s.I(), s.I(),
          IDiskOp(diskOp(IIO(io))).bdop)
  {
    if counter == 0 {
      res := None;
      assert IOModel.noop(old_s.I(), s.I());
    } else {
      var incache := s.cache.InCache(ref);
      if !incache {
        PageInNodeReqOrMakeRoom(inout s, io, ref);
        res := None;
      } else {
        ghost var node := s.cache.I()[ref];
        assert s.cache.I() == old(s.cache.I());

        var pivots, edges, children := s.cache.GetNodeInfo(ref);
        var boundedkey := ComputeBoundedKey(pivots, key);
        if !boundedkey {
          res := None;
          assert IOModel.noop(old_s.I(), s.I());
        } else {
          ghost var oldIVars := s.I();
          LruModel.LruUse(s.lru.Queue(), ref);
          inout s.lru.Use(ref);

          ghost var node := s.cache.I()[ref];
              
          var r := Pivots.ComputeRoute(pivots, key);
          ghost var bucket := node.buckets[r];
          var kmtMsg := s.cache.GetMessage(ref, r, key);
          var newmsg := if kmtMsg.Some? then ValueMessage.Merge(msg, kmtMsg.value) else msg;

          ghost var newlookup := new_lookup(lookup, ref, node, key);
          AugmentLookup(newlookup, lookup, querykey, ref, node, key, s.cache.I(), s.ephemeralIndirectionTable.graph);

          assert BT.LookupVisitsWellMarshalledBuckets(newlookup) ==> 
            && BucketWellMarshalled(bucket) 
            && BT.LookupVisitsWellMarshalledBuckets(lookup);

          if (newmsg.Define?) {
            res := Some(newmsg.value);
            assert BT.ValidQuery(BT.LookupQuery(querykey, res.value, newlookup));

            assert BBC.BetreeMove(old_s.I(), s.I(),
                IDiskOp(diskOp(IIO(io))).bdop,
                AdvanceOp(UI.GetOp(querykey, res.value), false),
                BT.BetreeQuery(BT.LookupQuery(querykey, res.value, newlookup)));

            assert IOModel.stepsBetree(old_s.I(), s.I(),
                AdvanceOp(UI.GetOp(querykey, res.value), false),
                BT.BetreeQuery(BT.LookupQuery(querykey, res.value, newlookup)));
          } else {
            if children.Some? {
              BookkeepingModel.lemmaChildInGraph(s.I(), ref, children.value[r]);
              var newkey := ComputeTranslateKey(pivots, edges, key, r);
              res := queryIterate(inout s, querykey, newkey, newmsg, children.value[r], io, counter - 1, newlookup);
            } else {
              res := Some(ValueType.DefaultValue());
              assert BC.OpTransaction(old_s.I(), s.I(),
                BT.BetreeStepOps(BT.BetreeQuery(BT.LookupQuery(querykey, res.value, newlookup))));

              assert BBC.BetreeMove(old_s.I(), s.I(),
                IDiskOp(diskOp( IIO(io) )).bdop,
                AdvanceOp(UI.GetOp(querykey, res.value), false),
                BT.BetreeQuery(BT.LookupQuery(querykey, res.value, newlookup)));

              assert IOModel.stepsBetree(old_s.I(), s.I(),
                AdvanceOp(UI.GetOp(querykey, res.value), false),
                BT.BetreeQuery(BT.LookupQuery(querykey, res.value, newlookup)));
            }
          }
        }
      }
    }
  }

  method query(linear inout s: ImplVariables, io: DiskIOHandler, key: Key)
  returns (res: Option<Value>)
  requires old_s.Inv() && old_s.Ready?
  requires io.initialized()

  modifies io

  ensures s.WFBCVars()
  ensures ValidDiskOp(diskOp(IIO(io)))
  ensures IDiskOp(diskOp(IIO(io))).jdop.NoDiskOp?
  ensures res.Some? ==>
      BBC.Next(old_s.I(), s.I(),
          IDiskOp(diskOp(IIO(io))).bdop,
          AdvanceOp(UI.GetOp(key, res.value), false));
  ensures res.None? ==>
      IOModel.betree_next_dop(old_s.I(), s.I(),
          IDiskOp(diskOp(IIO(io))).bdop)
  {
    var ref := BT.G.Root();
    var msg := ValueMessage.IdentityMessage();
    var counter: uint64 := 40;

    res := queryIterate(inout s, key, key, msg, ref, io, counter, []);
  }
}
