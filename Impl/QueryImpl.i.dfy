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
  import opened DiskOpModel

  import PBS = PivotBetreeSpec`Internal
  import opened InterpretationDiskOps
  import opened ViewOp

  // == query ==

  method queryIterate(linear inout s: ImplVariables, key: Key, msg: Message, ref: BT.G.Reference, io: DiskIOHandler, counter: uint64, ghost lookup: seq<BT.G.ReadOp>)
  returns (res: Option<Value>)

  requires old_s.W() && old_s.BCInv()
  requires queryInv(old_s.IBlockCache(), key, msg, ref, IIO(io), counter, lookup)
  requires !msg.Define?
  requires io.initialized()

  modifies io
  decreases counter
  ensures s.W()

  ensures ValidDiskOp(diskOp(IIO(io)))
  ensures IDiskOp(diskOp(IIO(io))).jdop.NoDiskOp?
  ensures res.Some? ==>
      BBC.Next(old_s.IBlockCache(), s.IBlockCache(),
          IDiskOp(diskOp(IIO(io))).bdop,
          AdvanceOp(UI.GetOp(key, res.value), false));
  ensures res.None? ==>
      IOModel.betree_next_dop(old_s.IBlockCache(), s.IBlockCache(),
          IDiskOp(diskOp(IIO(io))).bdop)
  {
    if counter == 0 {
      res := None;
      assert IOModel.noop(old_s.IBlockCache(), s.IBlockCache());
    } else {
      var incache := s.cache.InCache(ref);
      if !incache {
        PageInNodeReqOrMakeRoom(inout s, io, ref);
        res := None;
      } else {
        ghost var node := s.cache.I()[ref];

        assert s.cache.I() == old(s.cache.I());
        var pivots, children := s.cache.GetNodeInfo(ref);

        var boundedkey := ComputeBoundedKey(pivots, key);
        if !boundedkey {
          res := None;
          assert IOModel.noop(old_s.IBlockCache(), s.IBlockCache());
        } else {
          ghost var oldIVars := s.IBlockCache();
          LruModel.LruUse(s.lru.Queue(), ref);
          inout s.lru.Use(ref);
          assert oldIVars == s.IBlockCache();

          var r := Pivots.ComputeRoute(pivots, key);
          ghost var bucket := node.buckets[r];

          var kmtMsg := s.cache.GetMessage(ref, r, key);
          var newmsg := if kmtMsg.Some? then ValueMessage.Merge(msg, kmtMsg.value) else msg;

          ghost var newlookup := new_lookup(lookup, ref, node);
          AugmentLookup(newlookup, lookup, ref, node, key, s.cache.I(), s.ephemeralIndirectionTable.graph);

          assert PBS.LookupVisitsWellMarshalledBuckets(newlookup, key) ==> BucketWellMarshalled(bucket);
          assert PBS.LookupVisitsWellMarshalledBuckets(newlookup, key) ==> PBS.LookupVisitsWellMarshalledBuckets(lookup, key)
          by {
            reveal_new_lookup();
          }

          if (newmsg.Define?) {
            res := Some(newmsg.value);

            assert BT.ValidQuery(BT.LookupQuery(key, res.value, newlookup));
            assert BBC.BetreeMove(old_s.IBlockCache(), s.IBlockCache(),
              IDiskOp(diskOp(IIO(io))).bdop,
              AdvanceOp(UI.GetOp(key, res.value), false),
              BT.BetreeQuery(BT.LookupQuery(key, res.value, newlookup)));
            assert IOModel.stepsBetree(old_s.IBlockCache(), s.IBlockCache(),
              AdvanceOp(UI.GetOp(key, res.value), false),
              BT.BetreeQuery(BT.LookupQuery(key, res.value, newlookup)));
          } else {
            if children.Some? {
              BookkeepingModel.lemmaChildInGraph(s.IBlockCache(), ref, children.value[r]);
              res := queryIterate(inout s, key, newmsg, children.value[r], io, counter - 1, newlookup);
            } else {
              res := Some(ValueType.DefaultValue());
              assert BC.OpTransaction(old_s.IBlockCache(), s.IBlockCache(),
                PBS.BetreeStepOps(BT.BetreeQuery(BT.LookupQuery(key, res.value, newlookup))));

              assert BBC.BetreeMove(old_s.IBlockCache(), s.IBlockCache(),
                IDiskOp(diskOp( IIO(io) )).bdop,
                AdvanceOp(UI.GetOp(key, res.value), false),
                BT.BetreeQuery(BT.LookupQuery(key, res.value, newlookup)));

              assert IOModel.stepsBetree(old_s.IBlockCache(), s.IBlockCache(),
                AdvanceOp(UI.GetOp(key, res.value), false),
                BT.BetreeQuery(BT.LookupQuery(key, res.value, newlookup)));
            }
          }
        }
      }
    }
  }

  method query(linear inout s: ImplVariables, io: DiskIOHandler, key: Key)
  returns (res: Option<Value>)
  requires old_s.BCInv() && old_s.Ready?
  requires io.initialized()

  modifies io

  ensures s.W()
  ensures ValidDiskOp(diskOp(IIO(io)))
  ensures IDiskOp(diskOp(IIO(io))).jdop.NoDiskOp?
  ensures res.Some? ==>
      BBC.Next(old_s.IBlockCache(), s.IBlockCache(),
          IDiskOp(diskOp(IIO(io))).bdop,
          AdvanceOp(UI.GetOp(key, res.value), false));
  ensures res.None? ==>
      IOModel.betree_next_dop(old_s.IBlockCache(), s.IBlockCache(),
          IDiskOp(diskOp(IIO(io))).bdop)
  {
    var ref := BT.G.Root();
    var msg := ValueMessage.IdentityMessage();
    var counter: uint64 := 40;

    res := queryIterate(inout s, key, msg, ref, io, counter, []);
  }
}
