include "Impl.i.dfy"
include "ImplSync.i.dfy"
include "ImplModelQuery.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Option.s.dfy"
include "../lib/Sets.i.dfy"
include "PivotBetreeSpec.i.dfy"

// See dependency graph in MainImpl.dfy

module ImplQuery { 
  import opened Impl
  import opened ImplSync
  import opened ImplIO
  import ImplModelQuery
  import ImplModelCache
  import opened ImplState

  import opened Options
  import opened NativeTypes
  import opened Maps
  import opened Sets
  import opened Sequences

  import opened Bounds
  import opened BucketsLib
  import PivotsLib

  import opened PBS = PivotBetreeSpec`Spec

  // == query ==

  method TryRootBucketLookup(k: ImplConstants, s: ImplVariables, key: MS.Key)
  returns (res: Option<MS.Value>)
  requires Inv(k, s)
  requires s.ready
  ensures res == ImplModelQuery.TryRootBucketLookup(Ic(k), s.I(), key)
  {
    var qres := TTT.Query(s.rootBucket, key);
    if (qres.ValueForKey?) {
      res := Some(qres.value.value);
    } else {
      res := None;
    }
  }

  method query(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, key: MS.Key)
  returns (res: Option<MS.Value>)
  requires io.initialized()
  requires Inv(k, s)
  requires io !in s.Repr()
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures (s.I(), res, IIO(io)) == ImplModelQuery.query(Ic(k), old(s.I()), old(IIO(io)), key)
  {
    ImplModelQuery.reveal_query();
    ImplModelQuery.reveal_queryIterate();

    if (!s.ready) {
      PageInIndirectionTableReq(k, s, io);
      res := None;
    } else {
      var rootLookup := TryRootBucketLookup(k, s, key);
      if (rootLookup.Some?) {
        res := rootLookup;
        return;
      }

      var ref := BT.G.Root();
      var msg := Messages.IdentityMessage();
      var counter: uint64 := 40;

      while true
      invariant Inv(k, s)
      invariant s.ready
      invariant ref in IM.IIndirectionTable(IIndirectionTable(s.ephemeralIndirectionTable)).graph
      invariant io.initialized()
      invariant ImplModelQuery.query(Ic(k), old(s.I()), old(IIO(io)), key)
             == ImplModelQuery.queryIterate(Ic(k), s.I(), key, msg, ref, IIO(io), counter)
      invariant counter as int >= 0
      invariant io !in s.Repr()
      invariant WellUpdated(s)
      decreases counter as int
      {
        if counter == 0 {
          res := None;
          return;
        }

        if (ref !in s.cache) {
          if |s.cache| + |s.outstandingBlockReads| <= MaxCacheSize() - 1 {
            PageInReq(k, s, io, ref);
            res := None;
            return;
          } else {
            res := None;
            return;
          }
        } else {
          var node := s.cache[ref];

          ghost var oldIVars := s.I();
          LruModel.LruUse(s.lru.Queue, ref);
          s.lru.Use(ref);
          assert IM.IVars(oldIVars) == IM.IVars(s.I());

          var r := Pivots.ComputeRoute(node.pivotTable, key);
          var bucket := node.buckets[r];

          var kmtMsg := KMTable.Query(bucket, key);
          var newmsg := if kmtMsg.Some? then Messages.Merge(msg, kmtMsg.value) else msg;

          if (newmsg.Define?) {
            res := Some(newmsg.value);
            return;
          } else {
            if node.children.Some? {
              ImplModelCache.lemmaChildInGraph(Ic(k), s.I(), ref, node.children.value[r]);
              counter := counter - 1;
              ref := node.children.value[r];
            } else {
              res := Some(MS.V.DefaultValue());
              return;
            }
          }
        }
      }
    }
  }
}
