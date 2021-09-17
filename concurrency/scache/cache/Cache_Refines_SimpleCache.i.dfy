include "SimpleCacheSM.i.dfy"
include "CacheSM.i.dfy"
include "../Constants.i.dfy"
include "CacheInv.i.dfy"

module DiskSSM_Refines_SimpleCachine
  refines Refinement(CrashAsyncIfc(CacheIfc),
        AsyncDiskSystemStateMachine(CacheIfc, CacheSSM),
        SimpleCacheStateMachine)
{
  import opened Constants
  import opened NativeTypes
  import opened RequestIds
  import opened CacheStatusType
  import opened Options
  import opened CacheSSM
  import CacheIfc
  import DiskIfc
  import AsyncDisk
  import opened CacheInv

  predicate Inv(s: A.Variables)
  {
    CacheInv.Inv(s)
  }

  lemma InitImpliesInv(s: A.Variables)
  //requires A.Init(s)
  ensures Inv(s)
  {
    CacheInv.InitImpliesInv(s);
  }

  lemma NextPreservesInv(s: A.Variables, s': A.Variables, op: ifc.Op)
  //requires Inv(s)
  //requires A.Next(s, s', op)
  ensures Inv(s')
  {
    CacheInv.NextPreservesInv(s, s', op);
  }

  function IEntry(d: nat, entries: map<nat, Entry>, statuses: map<nat, Status>) : B.Entry
  requires d in entries && entries[d].Entry? ==> d in statuses
  {
    if d in entries then
      match entries[d] {
        case Empty => B.Empty
        case Reading(disk_idx) => B.Reading(disk_idx)
        case Entry(disk_idx, data) =>
          match statuses[d] {
            case Clean => B.Clean(disk_idx, data)
            case Dirty => B.Dirty(disk_idx, data)
            case Writeback => B.Writeback(disk_idx, data)
          }
      }
    else B.Empty
  }

  function IEntries(entries: map<nat, Entry>, statuses: map<nat, Status>) : imap<nat, B.Entry>
  requires forall d :: d in entries && entries[d].Entry? ==> d in statuses
  {
    imap d | B.True(d) :: IEntry(d, entries, statuses)
  }

  function easy_union<K(!new),V>(m1: map<K, V>, m2: map<K, V>) : map<K, V> {
    map k | k in m1.Keys + m2.Keys ::
        if k in m1 then m1[k] else m2[k]
  }

  function {:opaque} map_of_write_reqs(m: map<RequestId, DiskIfc.ReqWrite>) : map<nat, seq<byte>>
  requires forall rid1, rid2 | rid1 in m && rid2 in m && rid1 != rid2 :: m[rid1].addr != m[rid2].addr
  {
    map rid | rid in m :: m[rid].addr := m[rid].data
  }

  function {:opaque} map_of_read_resps(m: map<RequestId, DiskIfc.RespRead>) : map<nat, seq<byte>>
  requires forall rid1, rid2 | rid1 in m && rid2 in m && rid1 != rid2 :: m[rid1].addr != m[rid2].addr
  {
    map rid | rid in m :: m[rid].addr := m[rid].data
  }

  function set_of_read_reqs(m: map<RequestId, DiskIfc.ReqRead>) : set<nat> {
    set rid | rid in m :: m[rid].addr
  }

  function set_of_write_resps(m: map<RequestId, DiskIfc.RespWrite>) : set<nat> {
    set rid | rid in m :: m[rid].addr
  }

  function IWriteReqs(mr: map<nat, DiskIfc.Block>, dr: map<RequestId, DiskIfc.ReqWrite>)
      : map<nat, seq<byte>>
  requires forall rid1, rid2 | rid1 in dr && rid2 in dr && rid1 != rid2 :: dr[rid1].addr != dr[rid2].addr
  {
    easy_union(mr, map_of_write_reqs(dr))
  }

  function IWriteResps(mr: set<nat>, dr: map<RequestId, DiskIfc.RespWrite>)
      : set<nat>
  {
    mr + set_of_write_resps(dr)
  }

  function IReadReqs(mr: set<nat>, dr: map<RequestId, DiskIfc.ReqRead>)
      : set<nat>
  {
    mr + set_of_read_reqs(dr)
  }

  function IReadResps(mr: map<nat, DiskIfc.Block>, dr: map<RequestId, DiskIfc.RespRead>)
      : map<nat, seq<byte>>
  requires forall rid1, rid2 | rid1 in dr && rid2 in dr && rid1 != rid2 :: dr[rid1].addr != dr[rid2].addr
  {
    easy_union(mr, map_of_read_resps(dr))
  }

  function IDisk(contents: map<nat, DiskIfc.Block>) : imap<nat, seq<byte>> {
    imap addr | addr in contents :: contents[addr]
  }

  function I(s: A.Variables) : B.Variables
  //requires Inv(s)
  {
    B.Variables(
      IEntries(s.machine.entries, s.machine.statuses),
      IWriteReqs(s.machine.write_reqs, s.disk.reqWrites),
      IWriteResps(s.machine.write_resps, s.disk.respWrites),
      IReadReqs(s.machine.read_reqs, s.disk.reqReads),
      IReadResps(s.machine.read_resps, s.disk.respReads),
      s.machine.tickets,
      s.machine.stubs,
      IDisk(s.disk.contents),
      s.machine.sync_reqs
    )
  }

  lemma InitRefinesInit(s: A.Variables)
  //requires A.Init(s)
  //requires Inv(s)
  ensures B.Init(I(s))
  {
    assert I(s).write_reqs == map[] by {
      reveal_map_of_write_reqs();
    }
    assert I(s).read_resps == map[] by {
      reveal_map_of_read_resps();
    }
    assert I(s).entries == (imap k | B.True(k) :: B.Empty) by {
      forall k | B.True(k)
      ensures I(s).entries[k] == B.Empty
      { }
    }
  }

  lemma Start_Refines(s: A.Variables, s': A.Variables, rid: RequestId, input: CacheIfc.Input)
  requires Inv(s)
  requires A.NewTicket(s, s', rid, input)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.Start(rid, input))
  {
    assume false;
    assert s'.machine.entries == s.machine.entries;
    assert s'.machine.statuses == s.machine.statuses;
    assert s'.machine.read_reqs == s.machine.read_reqs;
    assert s'.machine.read_resps == s.machine.read_resps;
    assert s'.machine.write_reqs == s.machine.write_reqs;
    assert s'.machine.write_resps == s.machine.write_resps;

    assert forall i :: InverseMapConsistent(s.machine, i) ==> InverseMapConsistent(s'.machine, i);
    assert forall i :: IsReading(s.machine, i) ==> IsReading(s'.machine, i);
    assert forall i :: IsWriting(s.machine, i) ==> IsWriting(s'.machine, i);
  }

  lemma End_Refines(s: A.Variables, s': A.Variables, rid: RequestId, output: CacheIfc.Output)
  requires Inv(s)
  requires A.ConsumeStub(s, s', rid, output)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.End(rid, output))
  {
    assume false;
    assert s'.machine.entries == s.machine.entries;
    assert s'.machine.statuses == s.machine.statuses;

    assert forall i :: InverseMapConsistent(s.machine, i) ==> InverseMapConsistent(s'.machine, i);
    assert forall i :: IsReading(s.machine, i) ==> IsReading(s'.machine, i);
    assert forall i :: IsWriting(s.machine, i) ==> IsWriting(s'.machine, i);
  }

  lemma StartRead_Refines(s: A.Variables, s': A.Variables, cache_idx: nat, disk_idx: nat)
  requires Inv(s)
  requires CacheSSM.StartRead(s.machine, s'.machine, cache_idx, disk_idx)
  requires s'.disk == s.disk
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert B.StartRead(I(s), I(s'), ifc.InternalOp,
          cache_idx, disk_idx);
    assert B.NextStep(I(s), I(s'), ifc.InternalOp,
          B.StartRead_Step(cache_idx, disk_idx));
  }

  lemma FinishRead_Refines(s: A.Variables, s': A.Variables, cache_idx: nat, disk_idx: nat)
  requires Inv(s)
  requires CacheSSM.FinishRead(s.machine, s'.machine, cache_idx, disk_idx)
  requires s'.disk == s.disk
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert disk_idx !in map_of_read_resps(s.disk.respReads) by {
      reveal_map_of_read_resps();
    }
    assert B.FinishRead(I(s), I(s'), ifc.InternalOp,
          cache_idx, disk_idx);
    assert B.NextStep(I(s), I(s'), ifc.InternalOp,
          B.FinishRead_Step(cache_idx, disk_idx));
  }

  lemma StartWriteback_Refines(s: A.Variables, s': A.Variables, cache_idx: nat)
  requires Inv(s)
  requires CacheSSM.StartWriteback(s.machine, s'.machine, cache_idx)
  requires s'.disk == s.disk
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    var disk_idx := s.machine.entries[cache_idx].disk_idx;
    assert B.StartWriteback(I(s), I(s'), ifc.InternalOp,
          cache_idx, disk_idx);
    assert B.NextStep(I(s), I(s'), ifc.InternalOp,
          B.StartWriteback_Step(cache_idx, disk_idx));
  }

  lemma FinishWriteback_Refines(s: A.Variables, s': A.Variables, cache_idx: nat)
  requires Inv(s)
  requires CacheSSM.FinishWriteback(s.machine, s'.machine, cache_idx)
  requires s'.disk == s.disk
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    var disk_idx := s.machine.entries[cache_idx].disk_idx;
    assert B.FinishWriteback(I(s), I(s'), ifc.InternalOp,
          cache_idx, disk_idx);
    assert B.NextStep(I(s), I(s'), ifc.InternalOp,
          B.FinishWriteback_Step(cache_idx, disk_idx));
  }

  lemma Evict_Refines(s: A.Variables, s': A.Variables, cache_idx: nat)
  requires Inv(s)
  requires CacheSSM.Evict(s.machine, s'.machine, cache_idx)
  requires s'.disk == s.disk
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert B.Evict(I(s), I(s'), ifc.InternalOp,
          cache_idx);
    assert B.NextStep(I(s), I(s'), ifc.InternalOp,
          B.Evict_Step(cache_idx));
  }

  lemma ObserveCleanForSync_Refines(s: A.Variables, s': A.Variables, cache_idx: nat, rid: RequestId)
  requires Inv(s)
  requires CacheSSM.ObserveCleanForSync(s.machine, s'.machine, cache_idx, rid)
  requires s'.disk == s.disk
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert B.ObserveCleanForSync(I(s), I(s'), ifc.InternalOp,
          rid, cache_idx);
    assert B.NextStep(I(s), I(s'), ifc.InternalOp,
          B.ObserveCleanForSync_Step(rid, cache_idx));
  }

  lemma ApplyRead_Refines(s: A.Variables, s': A.Variables, cache_idx: nat, rid: RequestId)
  requires Inv(s)
  requires CacheSSM.ApplyRead(s.machine, s'.machine, cache_idx, rid)
  requires s'.disk == s.disk
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert B.ApplyRead(I(s), I(s'), ifc.InternalOp,
          rid, cache_idx);
    assert B.NextStep(I(s), I(s'), ifc.InternalOp,
          B.ApplyRead_Step(rid, cache_idx));
  }

  lemma ApplyWrite_Refines(s: A.Variables, s': A.Variables, cache_idx: nat, rid: RequestId)
  requires Inv(s)
  requires CacheSSM.ApplyWrite(s.machine, s'.machine, cache_idx, rid)
  requires s'.disk == s.disk
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert B.ApplyWrite(I(s), I(s'), ifc.InternalOp,
          rid, cache_idx);
    assert B.NextStep(I(s), I(s'), ifc.InternalOp,
          B.ApplyWrite_Step(rid, cache_idx));
  }

  lemma MarkDirty_Refines(s: A.Variables, s': A.Variables, cache_idx: nat)
  requires Inv(s)
  requires CacheSSM.MarkDirty(s.machine, s'.machine, cache_idx)
  requires s'.disk == s.disk
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assume false;
    //assert B.MarkDirty(I(s), I(s'), ifc.InternalOp, cache_idx);
    //assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.MarkDirty_Step(cache_idx));
  }

  lemma Machine_Internal_Refines(s: A.Variables, s': A.Variables)
  requires Inv(s)
  requires Internal(s.machine, s'.machine)
  requires s.disk == s'.disk
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    var step :| CacheSSM.InternalStep(s.machine, s'.machine, step);
    match step {
      case StartReadStep(cache_idx, disk_idx) =>
        StartRead_Refines(s, s', cache_idx, disk_idx);

      case FinishReadStep(cache_idx, disk_idx) => 
        FinishRead_Refines(s, s', cache_idx, disk_idx);

      case StartWritebackStep(cache_idx) =>
        StartWriteback_Refines(s, s', cache_idx);

      case FinishWritebackStep(cache_idx) =>
        FinishWriteback_Refines(s, s', cache_idx);

      case EvictStep(cache_idx) =>
        Evict_Refines(s, s', cache_idx);

      case ObserveCleanForSyncStep(cache_idx, rid) =>
        ObserveCleanForSync_Refines(s, s', cache_idx, rid);

      case ApplyReadStep(cache_idx, rid) =>
        ApplyRead_Refines(s, s', cache_idx, rid);

      case ApplyWriteStep(cache_idx, rid) =>
        ApplyWrite_Refines(s, s', cache_idx, rid);

      case MarkDirtyStep(cache_idx) =>
        MarkDirty_Refines(s, s', cache_idx);
    }
  }

  lemma ProcessRead_Refines(s: A.Variables, s': A.Variables, id: RequestId)
  requires Inv(s)
  requires AsyncDisk.ProcessRead(s.disk, s'.disk, id)
  requires s.machine == s'.machine
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    var disk_idx := s.disk.reqReads[id].addr;

    assert IReadResps(s'.machine.read_resps, s'.disk.respReads)
        == IReadResps(s.machine.read_resps, s.disk.respReads)[disk_idx := I(s).disk[disk_idx]]
    by {
      assert map_of_read_resps(s'.disk.respReads)
          == map_of_read_resps(s.disk.respReads)[disk_idx := s.disk.contents[disk_idx]]
      by {
        var x := map_of_read_resps(s.disk.respReads);
        var y := map_of_read_resps(s'.disk.respReads);
        assert disk_idx in y && y[disk_idx] == s.disk.contents[disk_idx] by {
          assert s'.disk.respReads[id].addr == disk_idx;
          assert s'.disk.respReads[id].data == s.disk.contents[disk_idx];
          reveal_map_of_read_resps();
        }
        forall k | k in x && k != disk_idx
        ensures k in y && x[k] == y[k]
        {
          /*
          assert exists rid :: rid in s.disk.respReads
              && s.disk.respReads[rid].addr == k by { reveal_map_of_read_resps(); }
          var rid :| rid in s.disk.respReads
              && s.disk.respReads[rid].addr == k;
          assert rid != id;
          assert rid in s'.disk.respReads
              && s'.disk.respReads[rid].addr == k;
          */
          reveal_map_of_read_resps();
        }
        forall k | k in y && k != disk_idx
        ensures k in x
        {
          reveal_map_of_read_resps();
        }
      }
    }

    assert IReadReqs(s'.machine.read_reqs, s'.disk.reqReads)
        == IReadReqs(s.machine.read_reqs, s.disk.reqReads) - {disk_idx}
    by {
      //assert disk_idx !in s'.machine.read_reqs;
      //assert disk_idx !in set_of_read_reqs(s'.disk.reqReads);
      //forall k | k != disk_idx && k in set_of_read_reqs(s'.disk.reqReads)
      //ensures k in set_of_read_reqs(s.disk.reqReads)
      //{
      //}
      forall k | k != disk_idx && k in set_of_read_reqs(s.disk.reqReads)
      ensures k in set_of_read_reqs(s'.disk.reqReads)
      {
        var y :| y in s.disk.reqReads && s.disk.reqReads[y].addr == k;
        assert s'.disk.reqReads[y].addr == k;
      }
      //assert set_of_read_reqs(s'.disk.reqReads)
      //      == set_of_read_reqs(s.disk.reqReads) - {disk_idx};
    }

    assert I(s).entries == I(s').entries;
    assert I(s).write_reqs == I(s').write_reqs;
    assert I(s).write_resps == I(s').write_resps;
    assert I(s).tickets == I(s').tickets;
    assert I(s).stubs == I(s').stubs;
    assert I(s).disk == I(s').disk;
    assert I(s).sync_reqs == I(s').sync_reqs;

    assert B.ProcessRead(I(s), I(s'), ifc.InternalOp, disk_idx);
    assert B.NextStep(I(s), I(s'), ifc.InternalOp,
          B.ProcessRead_Step(disk_idx));
  }

  lemma ProcessWrite_Refines(s: A.Variables, s': A.Variables, id: RequestId)
  requires Inv(s)
  requires AsyncDisk.ProcessWrite(s.disk, s'.disk, id)
  requires s.machine == s'.machine
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    var disk_idx := s.disk.reqWrites[id].addr;

    assert IWriteResps(s'.machine.write_resps, s'.disk.respWrites)
        == IWriteResps(s.machine.write_resps, s.disk.respWrites) + {disk_idx}
    by {
      assert set_of_write_resps(s'.disk.respWrites)
          == set_of_write_resps(s.disk.respWrites) + {disk_idx}
      by {
        var x := set_of_write_resps(s.disk.respWrites);
        var y := set_of_write_resps(s'.disk.respWrites);
        assert disk_idx in y by {
          assert s'.disk.respWrites[id].addr == disk_idx;
        }
        forall k | k != disk_idx && k in x ensures k in y {
          var rid :| rid in s.disk.respWrites && s.disk.respWrites[rid].addr == k;
          assert rid in s'.disk.respWrites && s'.disk.respWrites[rid].addr == k;
        }
        forall k | k != disk_idx && k in y ensures k in x {
        }
      }
    }

    assert disk_idx in IWriteReqs(s.machine.write_reqs, s.disk.reqWrites)
    by {
      assert disk_idx in map_of_write_reqs(s.disk.reqWrites)
      by {
        reveal_map_of_write_reqs();
      }
    }

    assert IWriteReqs(s'.machine.write_reqs, s'.disk.reqWrites)
        == IWriteReqs(s.machine.write_reqs, s.disk.reqWrites) - {disk_idx}
    by {
      assert map_of_write_reqs(s'.disk.reqWrites)
          == map_of_write_reqs(s.disk.reqWrites) - {disk_idx}
      by {
        var x := map_of_write_reqs(s.disk.reqWrites);
        var y := map_of_write_reqs(s'.disk.reqWrites);
        assert disk_idx !in y
        by {
          reveal_map_of_write_reqs();
        }
        forall k | k in x && k != disk_idx
        ensures k in y && x[k] == y[k]
        {
          assert exists rid :: rid in s.disk.reqWrites && s.disk.reqWrites[rid].addr == k
            by { reveal_map_of_write_reqs(); }
          var rid :| rid in s.disk.reqWrites && s.disk.reqWrites[rid].addr == k;
          assert rid != id;
          assert rid in s'.disk.reqWrites && s'.disk.reqWrites[rid].addr == k;
          reveal_map_of_write_reqs();
        }
        forall k | k in y && k != disk_idx
        ensures k in x
        {
          reveal_map_of_write_reqs();
        }
      }
    }

    assert IWriteReqs(s.machine.write_reqs, s.disk.reqWrites)[disk_idx]
      == s.disk.reqWrites[id].data
    by {
      reveal_map_of_write_reqs();
    }

    assert I(s').disk == I(s).disk[disk_idx := I(s).write_reqs[disk_idx]];

    assert I(s).entries == I(s').entries;
    assert I(s).read_reqs == I(s').read_reqs;
    assert I(s).read_resps == I(s').read_resps;
    assert I(s).tickets == I(s').tickets;
    assert I(s).stubs == I(s').stubs;
    assert I(s).sync_reqs == I(s').sync_reqs;

    assert B.ProcessWrite(I(s), I(s'), ifc.InternalOp, disk_idx);
    assert B.NextStep(I(s), I(s'), ifc.InternalOp,
          B.ProcessWrite_Step(disk_idx));
  }

  lemma HavocConflictingWrites_Refines(s: A.Variables, s': A.Variables, id: RequestId, id':RequestId)
  requires Inv(s)
  requires AsyncDisk.HavocConflictingWrites(s.disk, s'.disk, id, id')
  requires s.machine == s'.machine
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert false; // premises are impossible
  }

  lemma HavocConflictingWriteRead_Refines(s: A.Variables, s': A.Variables, id: RequestId,id': RequestId)
  requires Inv(s)
  requires AsyncDisk.HavocConflictingWriteRead(s.disk, s'.disk, id, id')
  requires s.machine == s'.machine
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert false; // premises are impossible
  }

  lemma DiskInternal_Refines(s: A.Variables, s': A.Variables)
  requires Inv(s)
  requires A.DiskInternal(s, s')
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    var step :| AsyncDisk.NextInternalStep(s.disk, s'.disk, step);
    match step {
      case ProcessReadStep(id) => ProcessRead_Refines(s, s', id);
      case ProcessWriteStep(id) => ProcessWrite_Refines(s, s', id);
      case HavocConflictingWritesStep(id, id') => HavocConflictingWrites_Refines(s, s', id, id');
      case HavocConflictingWriteReadStep(id, id') => HavocConflictingWriteRead_Refines(s, s', id, id');
    }
  }

  lemma Interaction_ReqWrite_Refines_helper(s: A.Variables, s': A.Variables, dop: DiskIfc.DiskOp)
  requires Inv(s)
  requires AsyncDisk.RecvWrite(s.disk, s'.disk, dop)
  //requires s.machine == CacheSSM.dot(s'.machine, CacheSSM.DiskWriteReq(dop.reqWrite.addr, dop.reqWrite.data))

  requires Inv(s')

  requires s.machine == s'.machine.(
    write_reqs := s'.machine.write_reqs[dop.reqWrite.addr := dop.reqWrite.data])

  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    var disk_idx := dop.reqWrite.addr;
    assert IWriteReqs(s'.machine.write_reqs, s'.disk.reqWrites)
        == IWriteReqs(s.machine.write_reqs, s.disk.reqWrites)
    by {
      assert disk_idx in IWriteReqs(s.machine.write_reqs, s.disk.reqWrites);
      assert disk_idx in IWriteReqs(s'.machine.write_reqs, s'.disk.reqWrites)
          && IWriteReqs(s.machine.write_reqs, s.disk.reqWrites)[disk_idx]
          == IWriteReqs(s'.machine.write_reqs, s'.disk.reqWrites)[disk_idx]
      by {
        assert s'.disk.reqWrites[dop.id].addr == disk_idx;
        reveal_map_of_write_reqs();
      }
      var x := map_of_write_reqs(s.disk.reqWrites);
      var y := map_of_write_reqs(s'.disk.reqWrites);
      forall k | k != disk_idx && k in x
      ensures k in y && y[k] == x[k]
      {
        reveal_map_of_write_reqs();
      }
      forall k | k != disk_idx && k in y
      ensures k in x
      {
        reveal_map_of_write_reqs();
      }
    }
    assert I(s) == I(s');
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.Stutter_Step);
  }

  lemma Interaction_RespWrite_Refines_helper(s: A.Variables, s': A.Variables, dop: DiskIfc.DiskOp)
  requires Inv(s)
  requires AsyncDisk.AckWrite(s.disk, s'.disk, dop)
  //requires s'.machine == CacheSSM.dot(s.machine, CacheSSM.DiskWriteResp(dop.respWrite.addr))
  requires s'.machine == s.machine.(
    write_resps := s.machine.write_resps + {dop.respWrite.addr})
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    var disk_idx := dop.respWrite.addr;
    assert IWriteResps(s'.machine.write_resps, s'.disk.respWrites)
        == IWriteResps(s.machine.write_resps, s.disk.respWrites)
    by {
      assert disk_idx in IWriteResps(s'.machine.write_resps, s'.disk.respWrites);
      assert disk_idx in IWriteResps(s.machine.write_resps, s.disk.respWrites);
      var x := set_of_write_resps(s.disk.respWrites);
      var y := set_of_write_resps(s'.disk.respWrites);
      forall k | k != disk_idx && k in x
      ensures k in y
      {
        var id :| id in s.disk.respWrites && s.disk.respWrites[id].addr == k;
        assert id != dop.id;
        assert id in s'.disk.respWrites && s'.disk.respWrites[id].addr == k;
      }
      forall k | k != disk_idx && k in y
      ensures k in x
      {
      }
    }
    assert I(s) == I(s');
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.Stutter_Step);
  }

  lemma Interaction_ReqRead_Refines_helper(s: A.Variables, s': A.Variables, dop: DiskIfc.DiskOp)
  requires Inv(s)
  requires AsyncDisk.RecvRead(s.disk, s'.disk, dop)
  //requires s.machine == CacheSSM.dot(s'.machine, CacheSSM.DiskReadReq(dop.reqRead.addr))
  requires Inv(s')
  requires s.machine == s'.machine.(
      read_reqs := s'.machine.read_reqs + {dop.reqRead.addr})
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    var disk_idx := dop.reqRead.addr;
    assert IReadReqs(s'.machine.read_reqs, s'.disk.reqReads)
        == IReadReqs(s.machine.read_reqs, s.disk.reqReads)
    by {
      assert disk_idx in IReadReqs(s'.machine.read_reqs, s'.disk.reqReads)
      by {
        assert s'.disk.reqReads[dop.id].addr == disk_idx;
      }
      assert disk_idx in IReadReqs(s.machine.read_reqs, s.disk.reqReads);
      var x := set_of_read_reqs(s.disk.reqReads);
      var y := set_of_read_reqs(s'.disk.reqReads);
      forall k | k != disk_idx && k in x
      ensures k in y
      {
        var id :| id in s.disk.reqReads && s.disk.reqReads[id].addr == k;
        assert id != dop.id;
        assert id in s'.disk.reqReads && s'.disk.reqReads[id].addr == k;
      }
      forall k | k != disk_idx && k in y
      ensures k in x
      {
      }
    }
    assert I(s) == I(s');
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.Stutter_Step);
  }

  lemma Interaction_RespRead_Refines_helper(s: A.Variables, s': A.Variables, dop: DiskIfc.DiskOp)
  requires Inv(s)
  requires AsyncDisk.AckRead(s.disk, s'.disk, dop)
  //requires s'.machine == CacheSSM.dot(s.machine, CacheSSM.DiskReadResp(dop.respRead.addr, dop.respRead.data))
  requires Inv(s')
  requires s'.machine == s.machine.(
      read_resps := s.machine.read_resps[dop.respRead.addr := dop.respRead.data])
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    var disk_idx := dop.respRead.addr;
    assert IReadResps(s'.machine.read_resps, s'.disk.respReads)
        == IReadResps(s.machine.read_resps, s.disk.respReads)
    by {
      assert disk_idx in IReadResps(s'.machine.read_resps, s'.disk.respReads);
      assert disk_idx in IReadResps(s.machine.read_resps, s.disk.respReads)
          && IReadResps(s'.machine.read_resps, s'.disk.respReads)[disk_idx]
          == IReadResps(s.machine.read_resps, s.disk.respReads)[disk_idx]
      by {
        assert s.disk.respReads[dop.id].addr == disk_idx;
        reveal_map_of_read_resps();
      }
      var x := map_of_read_resps(s.disk.respReads);
      var y := map_of_read_resps(s'.disk.respReads);
      forall k | k != disk_idx && k in x
      ensures k in y && y[k] == x[k]
      {
        assert exists rid :: rid in s.disk.respReads && s.disk.respReads[rid].addr == k by { reveal_map_of_read_resps(); }
        var rid :| rid in s.disk.respReads && s.disk.respReads[rid].addr == k;
        assert rid != dop.id;
        assert s'.disk.respReads[rid].addr == k;
        reveal_map_of_read_resps();
      }
      forall k | k != disk_idx && k in y
      ensures k in x
      {
        reveal_map_of_read_resps();
      }
    }
    assert I(s) == I(s');
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.Stutter_Step);
  }

  lemma Interaction_ReqWrite_Refines(s: A.Variables, s': A.Variables, dop: DiskIfc.DiskOp)
  requires Inv(s)
  requires AsyncDisk.RecvWrite(s.disk, s'.disk, dop)
  requires s.machine == CacheSSM.dot(s'.machine, CacheSSM.DiskWriteReq(dop.reqWrite.addr, dop.reqWrite.data))
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert s.machine.write_reqs ==
      s'.machine.write_reqs[dop.reqWrite.addr := dop.reqWrite.data];
    assert s.machine.disk_idx_to_cache_idx == s'.machine.disk_idx_to_cache_idx;
    assert s.machine.entries == s'.machine.entries;
    assert s.machine.statuses == s'.machine.statuses;
    assert s.machine.read_reqs == s'.machine.read_reqs;
    assert s.machine.read_resps == s'.machine.read_resps;
    assert s.machine.write_resps == s'.machine.write_resps;
    assert s.machine.tickets == s'.machine.tickets;
    assert s.machine.stubs == s'.machine.stubs;
    assert s.machine.sync_reqs == s'.machine.sync_reqs;
    Interaction_ReqWrite_Refines_helper(s, s', dop);
  }

  lemma Interaction_RespWrite_Refines(s: A.Variables, s': A.Variables, dop: DiskIfc.DiskOp)
  requires Inv(s)
  requires AsyncDisk.AckWrite(s.disk, s'.disk, dop)
  requires s'.machine == CacheSSM.dot(s.machine, CacheSSM.DiskWriteResp(dop.respWrite.addr))
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    Interaction_RespWrite_Refines_helper(s, s', dop);
  }

  lemma Interaction_ReqRead_Refines(s: A.Variables, s': A.Variables, dop: DiskIfc.DiskOp)
  requires Inv(s)
  requires AsyncDisk.RecvRead(s.disk, s'.disk, dop)
  requires s.machine == CacheSSM.dot(s'.machine, CacheSSM.DiskReadReq(dop.reqRead.addr))
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert s.machine.read_reqs ==
        s'.machine.read_reqs + {dop.reqRead.addr};
    assert s.machine.disk_idx_to_cache_idx == s'.machine.disk_idx_to_cache_idx;
    assert s.machine.entries == s'.machine.entries;
    assert s.machine.statuses == s'.machine.statuses;
    assert s.machine.write_reqs == s'.machine.write_reqs;
    assert s.machine.read_resps == s'.machine.read_resps;
    assert s.machine.write_resps == s'.machine.write_resps;
    assert s.machine.tickets == s'.machine.tickets;
    assert s.machine.stubs == s'.machine.stubs;
    Interaction_ReqRead_Refines_helper(s, s', dop);
  }

  lemma Interaction_RespRead_Refines(s: A.Variables, s': A.Variables, dop: DiskIfc.DiskOp)
  requires Inv(s)
  requires AsyncDisk.AckRead(s.disk, s'.disk, dop)
  requires s'.machine == CacheSSM.dot(s.machine, CacheSSM.DiskReadResp(dop.respRead.addr, dop.respRead.data))
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    Interaction_RespRead_Refines_helper(s, s', dop);
  }

  lemma Interaction_Refines(s: A.Variables, s': A.Variables, dop: DiskIfc.DiskOp)
  requires Inv(s)
  requires A.Interaction(s, s', dop)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    match dop {
      case ReqReadOp(id, reqRead) => {
        Interaction_ReqRead_Refines(s, s', dop);
      }
      case ReqWriteOp(id, reqWrite) => {
        Interaction_ReqWrite_Refines(s, s', dop);
      }
      case RespReadOp(id, respRead) => {
        Interaction_RespRead_Refines(s, s', dop);
      }
      case RespWriteOp(id, respWrite) => {
        Interaction_RespWrite_Refines(s, s', dop);
      }
    }
  }

  lemma Internal_Refines(s: A.Variables, s': A.Variables)
  requires Inv(s)
  requires A.Internal(s, s')
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    var step :| A.InternalStep(s, s', step);
    match step {
      case MachineStep(shard, shard', rest) => {
        InternalMonotonic(
            A.Variables(s.disk, shard),
            A.Variables(s.disk, shard'),
            rest);
        Machine_Internal_Refines(s, s');
      }
      case InteractionStep(dop) => {
        Interaction_Refines(s, s', dop);
      }
      case DiskInternalStep => {
        DiskInternal_Refines(s, s');
      }
    }
  }

  lemma Crash_Refines(s: A.Variables, s': A.Variables)
  requires Inv(s)
  requires A.Crash(s, s')
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.CrashOp)
  {
    InitImpliesInv(s');
    InitRefinesInit(s');
    assert B.Crash(I(s), I(s'), ifc.CrashOp);
    assert B.NextStep(I(s), I(s'), ifc.CrashOp, B.Crash_Step);
  }

  lemma NextRefinesNext(s: A.Variables, s': A.Variables, op: ifc.Op)
  //requires Inv(s)
  //requires A.Next(s, s', op)
  //requires Inv(s')
  ensures B.Next(I(s), I(s'), op)
  {
    match op {
      case Start(rid, input) => {
        Start_Refines(s, s', rid, input);
      }
      case End(rid, output) => {
        End_Refines(s, s', rid, output);
      }
      case CrashOp => {
        Crash_Refines(s, s');
      }
      case InternalOp => {
        Internal_Refines(s, s');
      }
    }
  }
}
