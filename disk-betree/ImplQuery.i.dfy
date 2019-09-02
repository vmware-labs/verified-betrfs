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
  requires s.Ready?
  ensures res == ImplModelQuery.TryRootBucketLookup(Ic(k), IVars(s), key)
  {
    var qres := TTT.Query(s.rootBucket, key);
    if (qres.ValueForKey?) {
      res := Some(qres.value.value);
    } else {
      res := None;
    }
  }

  method query(k: ImplConstants, s0: ImplVariables, io: DiskIOHandler, key: MS.Key)
  returns (s': ImplVariables, res: Option<MS.Value>)
  requires io.initialized()
  requires Inv(k, s0)
  modifies io
  ensures WVars(s')
  ensures (IVars(s'), res, IIO(io)) == ImplModelQuery.query(Ic(k), old(IVars(s0)), old(IIO(io)), key)
  {
    var s := s0;

    ImplModelQuery.reveal_query();
    ImplModelQuery.reveal_queryIterate();

    if (s.Unready?) {
      s' := PageInIndirectionTableReq(k, s, io);
      res := None;
    } else {
      var rootLookup := TryRootBucketLookup(k, s, key);
      if (rootLookup.Some?) {
        s' := s;
        res := rootLookup;
        return;
      }

      var ref := BT.G.Root();
      var msg := Messages.IdentityMessage();
      var counter: uint64 := 40;

      while true
      invariant Inv(k, s)
      invariant s.Ready?
      invariant ref in IM.IIndirectionTable(IIndirectionTable(s.ephemeralIndirectionTable)).graph
      invariant io.initialized()
      invariant ImplModelQuery.query(Ic(k), old(IVars(s0)), old(IIO(io)), key)
             == ImplModelQuery.queryIterate(Ic(k), IVars(s), key, msg, ref, IIO(io), counter)
      invariant counter as int >= 0
      decreases counter as int
      {
        if counter == 0 {
          s' := s;
          res := None;
          return;
        }

        if (ref !in s.cache) {
          if |s.cache| + |s.outstandingBlockReads| <= MaxCacheSize() - 1 {
            s' := PageInReq(k, s, io, ref);
            res := None;
            return;
          } else {
            s' := s;
            res := None;
            return;
          }
        } else {
          var node := s.cache[ref];

          var s1 := s.(lru := LruModel.Use(s.lru, ref));
          LruModel.LruUse(s.lru, ref);
          assert IM.IVars(IVars(s1)) == IM.IVars(IVars(s));
          s := s1;

          var r := Pivots.ComputeRoute(node.pivotTable, key);
          var bucket := node.buckets[r];

          var kmtMsg := KMTable.Query(bucket, key);
          var newmsg := if kmtMsg.Some? then Messages.Merge(msg, kmtMsg.value) else msg;

          if (newmsg.Define?) {
            s' := s;
            res := Some(newmsg.value);
            return;
          } else {
            if node.children.Some? {
              ImplModelCache.lemmaChildInGraph(Ic(k), IVars(s), ref, node.children.value[r]);
              counter := counter - 1;
              ref := node.children.value[r];
            } else {
              s' := s;
              res := Some(MS.V.DefaultValue());
              return;
            }
          }
        }
      }
    }
  }
}
