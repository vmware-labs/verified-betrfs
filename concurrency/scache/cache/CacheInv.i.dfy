include "SimpleCacheSM.i.dfy"
include "CacheSM.i.dfy"
include "../Constants.i.dfy"

module CacheInv {
  import ifc = CrashAsyncIfc(CacheIfc)
  import A = AsyncDiskSystemStateMachine(CacheIfc, CacheSSM)

  import opened Constants
  import opened RequestIds
  import opened Options
  import opened CacheSSM
  import CacheIfc
  import DiskIfc
  import AsyncDisk

  predicate IsReading(machine: CacheSSM.M, addr: nat)
  {
    && machine.M?
    && addr in machine.disk_idx_to_cache_idx
    && machine.disk_idx_to_cache_idx[addr].Some?
    && machine.disk_idx_to_cache_idx[addr].value in machine.entries
    && machine.entries[machine.disk_idx_to_cache_idx[addr].value].Reading?
  }

  predicate IsWriting(machine: CacheSSM.M, addr: nat)
  {
    && machine.M?
    && addr in machine.disk_idx_to_cache_idx
    && machine.disk_idx_to_cache_idx[addr].Some?
    && machine.disk_idx_to_cache_idx[addr].value in machine.statuses
    && machine.statuses[machine.disk_idx_to_cache_idx[addr].value].Writeback?
  }

  predicate InverseMapConsistent(machine: CacheSSM.M, i: nat)
  {
    && machine.M?
    && i in machine.disk_idx_to_cache_idx ==>
      && machine.disk_idx_to_cache_idx[i].Some? ==>
        && machine.disk_idx_to_cache_idx[i].value in machine.entries
        && (machine.entries[machine.disk_idx_to_cache_idx[i].value].Reading?
          || machine.entries[machine.disk_idx_to_cache_idx[i].value].Entry?)
        && machine.entries[machine.disk_idx_to_cache_idx[i].value].disk_idx == i
  }

  predicate Inv(s: A.Variables) {
    && s.machine.M?
    && (forall i :: i in s.machine.statuses <==>
        (i in s.machine.entries && s.machine.entries[i].Entry?))
    && (forall i | i in s.machine.entries ::
        (s.machine.entries[i].Entry? || s.machine.entries[i].Reading?) ==>
            s.machine.entries[i].disk_idx in s.machine.disk_idx_to_cache_idx &&
            s.machine.disk_idx_to_cache_idx[s.machine.entries[i].disk_idx] == Some(i))

    && (forall i :: InverseMapConsistent(s.machine, i))

    && s.disk.reqReads.Keys !! s.disk.respReads.Keys
    && s.disk.reqWrites.Keys !! s.disk.respWrites.Keys

    && s.machine.read_reqs !! s.machine.read_resps.Keys
    && (forall rid1, rid2 | rid1 in s.disk.reqReads && rid2 in s.disk.reqReads && rid1 != rid2 ::
          s.disk.reqReads[rid1].addr != s.disk.reqReads[rid2].addr)
    && (forall rid1, rid2 | rid1 in s.disk.respReads && rid2 in s.disk.respReads && rid1 != rid2 ::
          s.disk.respReads[rid1].addr != s.disk.respReads[rid2].addr)
    && (forall rid1, rid2 | rid1 in s.disk.reqReads && rid2 in s.disk.respReads ::
          s.disk.reqReads[rid1].addr != s.disk.respReads[rid2].addr)
    && (forall rid1 | rid1 in s.disk.reqReads :: s.disk.reqReads[rid1].addr !in s.machine.read_reqs)
    && (forall rid1 | rid1 in s.disk.reqReads :: s.disk.reqReads[rid1].addr !in s.machine.read_resps)
    && (forall rid2 | rid2 in s.disk.respReads :: s.disk.respReads[rid2].addr !in s.machine.read_reqs)
    && (forall rid2 | rid2 in s.disk.respReads :: s.disk.respReads[rid2].addr !in s.machine.read_resps)
    && (forall rid1 | rid1 in s.disk.reqReads :: IsReading(s.machine, s.disk.reqReads[rid1].addr))
    && (forall rid2 | rid2 in s.disk.respReads :: IsReading(s.machine, s.disk.respReads[rid2].addr))
    && (forall addr | addr in s.machine.read_reqs :: IsReading(s.machine, addr))
    && (forall addr | addr in s.machine.read_resps :: IsReading(s.machine, addr))

    && s.machine.write_reqs.Keys !! s.machine.write_resps
    && (forall rid1, rid2 | rid1 in s.disk.reqWrites && rid2 in s.disk.respWrites ::
          s.disk.reqWrites[rid1].addr != s.disk.respWrites[rid2].addr)
    && (forall rid1, rid2 | rid1 in s.disk.reqWrites && rid2 in s.disk.reqWrites && rid1 != rid2 ::
          s.disk.reqWrites[rid1].addr != s.disk.reqWrites[rid2].addr)
    && (forall rid1, rid2 | rid1 in s.disk.respWrites && rid2 in s.disk.respWrites && rid1 != rid2 ::
          s.disk.respWrites[rid1].addr != s.disk.respWrites[rid2].addr)
    && (forall rid1 | rid1 in s.disk.reqWrites :: s.disk.reqWrites[rid1].addr !in s.machine.write_reqs)
    && (forall rid1 | rid1 in s.disk.reqWrites :: s.disk.reqWrites[rid1].addr !in s.machine.write_resps)
    && (forall rid2 | rid2 in s.disk.respWrites :: s.disk.respWrites[rid2].addr !in s.machine.write_reqs)
    && (forall rid2 | rid2 in s.disk.respWrites :: s.disk.respWrites[rid2].addr !in s.machine.write_resps)
    && (forall rid1 | rid1 in s.disk.reqWrites :: IsWriting(s.machine, s.disk.reqWrites[rid1].addr))
    && (forall rid2 | rid2 in s.disk.respWrites :: IsWriting(s.machine, s.disk.respWrites[rid2].addr))
    && (forall addr | addr in s.machine.write_reqs :: IsWriting(s.machine, addr))
    && (forall addr | addr in s.machine.write_resps :: IsWriting(s.machine, addr))

    && s.machine.tickets.Keys !! s.machine.stubs.Keys
  }

  lemma InitImpliesInv(s: A.Variables)
  requires A.Init(s)
  ensures Inv(s)
  {
  }

  lemma Start_PreservesInv(s: A.Variables, s': A.Variables, rid: RequestId, input: CacheIfc.Input)
  requires Inv(s)
  requires A.NewTicket(s, s', rid, input)
  ensures Inv(s')
  {
    assert s'.machine.disk_idx_to_cache_idx == s.machine.disk_idx_to_cache_idx;
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

  lemma End_PreservesInv(s: A.Variables, s': A.Variables, rid: RequestId, output: CacheIfc.Output)
  requires Inv(s)
  requires A.ConsumeStub(s, s', rid, output)
  ensures Inv(s')
  {
    assert s'.machine.disk_idx_to_cache_idx == s.machine.disk_idx_to_cache_idx;
    assert s'.machine.entries == s.machine.entries;
    assert s'.machine.statuses == s.machine.statuses;
    assert s'.machine.read_reqs == s.machine.read_reqs;
    assert s'.machine.read_resps == s.machine.read_resps;
    assert s'.machine.write_reqs == s.machine.write_reqs;
    assert s'.machine.write_resps == s.machine.write_resps;


    assert forall i :: InverseMapConsistent(s.machine, i) ==> InverseMapConsistent(s'.machine, i);
    assert forall i :: IsReading(s.machine, i) ==> IsReading(s'.machine, i);
    assert forall i :: IsWriting(s.machine, i) ==> IsWriting(s'.machine, i);

    if !output.SyncOutput? && !output.HavocOutput? {
      assert s'.machine.stubs == s.machine.stubs - {rid};
    } else {
      assert s'.machine.stubs == s.machine.stubs;
    }
  }

  lemma StartRead_PreservesInv(s: A.Variables, s': A.Variables, cache_idx: nat, disk_idx: nat)
  requires Inv(s)
  requires CacheSSM.StartRead(s.machine, s'.machine, cache_idx, disk_idx)
  requires s'.disk == s.disk
  ensures Inv(s')
  {
    assert forall i :: InverseMapConsistent(s.machine, i) ==> InverseMapConsistent(s'.machine, i);
    assert forall i :: IsReading(s.machine, i) ==> IsReading(s'.machine, i);
    assert forall i :: IsWriting(s.machine, i) ==> IsWriting(s'.machine, i);
  }

  lemma FinishRead_PreservesInv(s: A.Variables, s': A.Variables, cache_idx: nat, disk_idx: nat)
  requires Inv(s)
  requires CacheSSM.FinishRead(s.machine, s'.machine, cache_idx, disk_idx)
  requires s'.disk == s.disk
  ensures Inv(s')
  {
    assert forall i :: InverseMapConsistent(s.machine, i) ==> InverseMapConsistent(s'.machine, i);
    forall i | i != disk_idx && IsReading(s.machine, i)
    ensures IsReading(s'.machine, i)
    {
      assert InverseMapConsistent(s.machine, i);
    }
    assert forall i :: IsWriting(s.machine, i) ==> IsWriting(s'.machine, i);
  }

  lemma StartWriteback_PreservesInv(s: A.Variables, s': A.Variables, cache_idx: nat)
  requires Inv(s)
  requires CacheSSM.StartWriteback(s.machine, s'.machine, cache_idx)
  requires s'.disk == s.disk
  ensures Inv(s')
  {
    assert forall i :: InverseMapConsistent(s.machine, i) ==> InverseMapConsistent(s'.machine, i);
    assert forall i :: IsReading(s.machine, i) ==> IsReading(s'.machine, i);
    assert forall i :: IsWriting(s.machine, i) ==> IsWriting(s'.machine, i);
  }

  lemma FinishWriteback_PreservesInv(s: A.Variables, s': A.Variables, cache_idx: nat)
  requires Inv(s)
  requires CacheSSM.FinishWriteback(s.machine, s'.machine, cache_idx)
  requires s'.disk == s.disk
  ensures Inv(s')
  {
    assert forall i :: InverseMapConsistent(s.machine, i) ==> InverseMapConsistent(s'.machine, i);
    assert forall i :: IsReading(s.machine, i) ==> IsReading(s'.machine, i);
    forall i | i != s.machine.entries[cache_idx].disk_idx && IsWriting(s.machine, i)
    ensures IsWriting(s'.machine, i);
    {
      assert InverseMapConsistent(s.machine, i);
    }
  }

  lemma Evict_PreservesInv(s: A.Variables, s': A.Variables, cache_idx: nat)
  requires Inv(s)
  requires CacheSSM.Evict(s.machine, s'.machine, cache_idx)
  requires s'.disk == s.disk
  ensures Inv(s')
  {
    assert forall i :: InverseMapConsistent(s.machine, i) ==> InverseMapConsistent(s'.machine, i);
    assert forall i :: IsReading(s.machine, i) ==> IsReading(s'.machine, i);
    assert forall i :: IsWriting(s.machine, i) ==> IsWriting(s'.machine, i);
  }

  lemma ObserveCleanForSync_PreservesInv(s: A.Variables, s': A.Variables, cache_idx: nat, rid: RequestId)
  requires Inv(s)
  requires CacheSSM.ObserveCleanForSync(s.machine, s'.machine, cache_idx, rid)
  requires s'.disk == s.disk
  ensures Inv(s')
  {
    assert forall i :: InverseMapConsistent(s.machine, i) ==> InverseMapConsistent(s'.machine, i);
    assert forall i :: IsReading(s.machine, i) ==> IsReading(s'.machine, i);
    assert forall i :: IsWriting(s.machine, i) ==> IsWriting(s'.machine, i);
  }

  lemma ApplyRead_PreservesInv(s: A.Variables, s': A.Variables, cache_idx: nat, rid: RequestId)
  requires Inv(s)
  requires CacheSSM.ApplyRead(s.machine, s'.machine, cache_idx, rid)
  requires s'.disk == s.disk
  ensures Inv(s')
  {
    assert forall i :: InverseMapConsistent(s.machine, i) ==> InverseMapConsistent(s'.machine, i);
    assert forall i :: IsReading(s.machine, i) ==> IsReading(s'.machine, i);
    assert forall i :: IsWriting(s.machine, i) ==> IsWriting(s'.machine, i);
  }

  lemma ApplyWrite_PreservesInv(s: A.Variables, s': A.Variables, cache_idx: nat, rid: RequestId)
  requires Inv(s)
  requires CacheSSM.ApplyWrite(s.machine, s'.machine, cache_idx, rid)
  requires s'.disk == s.disk
  ensures Inv(s')
  {
    assert forall i :: InverseMapConsistent(s.machine, i) ==> InverseMapConsistent(s'.machine, i);
    assert forall i :: IsReading(s.machine, i) ==> IsReading(s'.machine, i);
    assert forall i :: IsWriting(s.machine, i) ==> IsWriting(s'.machine, i);
  }

  lemma MarkDirty_PreservesInv(s: A.Variables, s': A.Variables, cache_idx: nat)
  requires Inv(s)
  requires CacheSSM.MarkDirty(s.machine, s'.machine, cache_idx)
  requires s'.disk == s.disk
  ensures Inv(s')
  {
    assert forall i :: InverseMapConsistent(s.machine, i) ==> InverseMapConsistent(s'.machine, i);
    assert forall i :: IsReading(s.machine, i) ==> IsReading(s'.machine, i);
    assert forall i :: IsWriting(s.machine, i) ==> IsWriting(s'.machine, i);
  }

  lemma HavocNew_PreservesInv(s: A.Variables, s': A.Variables, cache_idx: nat, rid: RequestId, block: DiskIfc.Block)
  requires Inv(s)
  requires CacheSSM.HavocNew(s.machine, s'.machine, cache_idx, rid, block)
  requires s'.disk == s.disk
  ensures Inv(s')
  {
    assert forall i :: InverseMapConsistent(s.machine, i) ==> InverseMapConsistent(s'.machine, i);
    assert forall i :: IsReading(s.machine, i) ==> IsReading(s'.machine, i);
    assert forall i :: IsWriting(s.machine, i) ==> IsWriting(s'.machine, i);
  }

  lemma HavocEvict_PreservesInv(s: A.Variables, s': A.Variables, cache_idx: nat, rid: RequestId)
  requires Inv(s)
  requires CacheSSM.HavocEvict(s.machine, s'.machine, cache_idx, rid)
  requires s'.disk == s.disk
  ensures Inv(s')
  {
    assert forall i :: InverseMapConsistent(s.machine, i) ==> InverseMapConsistent(s'.machine, i);
    assert forall i :: IsReading(s.machine, i) ==> IsReading(s'.machine, i);
    assert forall i :: IsWriting(s.machine, i) ==> IsWriting(s'.machine, i);
  }

  lemma StartRead_Monotonic(s: A.Variables, s': A.Variables, rest: CacheSSM.M,
      cache_idx: nat, disk_idx: nat)
  requires Inv(A.Variables(s.disk, CacheSSM.dot(s.machine, rest)))
  requires CacheSSM.StartRead(s.machine, s'.machine, cache_idx, disk_idx)
  ensures CacheSSM.Internal(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest))
  {
    /*assert disk_idx in s.machine.read_reqs ==> IsReading(s.machine, disk_idx);
    var f := CacheSSM.dot(s.machine, rest);
    var f' := CacheSSM.dot(s'.machine, rest);
    assert f'.M?;
    assert (f'.entries == f.entries[cache_idx := CacheSSM.Reading(disk_idx)]);
    assert (f'.disk_idx_to_cache_idx == f.disk_idx_to_cache_idx[disk_idx := Some(cache_idx)]);
    assert (f'.read_reqs == f.read_reqs + {disk_idx});*/
    assert CacheSSM.StartRead(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest), cache_idx, disk_idx);
    assert CacheSSM.InternalStep(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest), CacheSSM.StartReadStep(cache_idx, disk_idx));
  }

  lemma FinishRead_Monotonic(s: A.Variables, s': A.Variables, rest: CacheSSM.M,
      cache_idx: nat, disk_idx: nat)
  requires Inv(A.Variables(s.disk, CacheSSM.dot(s.machine, rest)))
  requires CacheSSM.FinishRead(s.machine, s'.machine, cache_idx, disk_idx)
  ensures CacheSSM.Internal(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest))
  {
    assert CacheSSM.InternalStep(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest), CacheSSM.FinishReadStep(cache_idx, disk_idx));
  }

  lemma StartWriteback_Monotonic(s: A.Variables, s': A.Variables, rest: CacheSSM.M,
      cache_idx: nat)
  requires Inv(A.Variables(s.disk, CacheSSM.dot(s.machine, rest)))
  requires CacheSSM.StartWriteback(s.machine, s'.machine, cache_idx)
  ensures CacheSSM.Internal(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest))
  {
    var disk_idx := s.machine.entries[cache_idx].disk_idx;
    var f := CacheSSM.dot(s.machine, rest);
    assert disk_idx in f.write_reqs ==> IsWriting(f, disk_idx);
    assert CacheSSM.StartWriteback(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest), cache_idx);
    assert CacheSSM.InternalStep(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest), CacheSSM.StartWritebackStep(cache_idx));
  }

  lemma FinishWriteback_Monotonic(s: A.Variables, s': A.Variables, rest: CacheSSM.M,
      cache_idx: nat)
  requires Inv(A.Variables(s.disk, CacheSSM.dot(s.machine, rest)))
  requires CacheSSM.FinishWriteback(s.machine, s'.machine, cache_idx)
  ensures CacheSSM.Internal(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest))
  {
    assert CacheSSM.InternalStep(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest), CacheSSM.FinishWritebackStep(cache_idx));
  }

  lemma Evict_Monotonic(s: A.Variables, s': A.Variables, rest: CacheSSM.M,
      cache_idx: nat)
  requires Inv(A.Variables(s.disk, CacheSSM.dot(s.machine, rest)))
  requires CacheSSM.Evict(s.machine, s'.machine, cache_idx)
  ensures CacheSSM.Internal(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest))
  {
    assert CacheSSM.InternalStep(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest), CacheSSM.EvictStep(cache_idx));
  }

  lemma ObserveCleanForSync_Monotonic(s: A.Variables, s': A.Variables, rest: CacheSSM.M,
      cache_idx: nat, rid: RequestId)
  requires Inv(A.Variables(s.disk, CacheSSM.dot(s.machine, rest)))
  requires CacheSSM.ObserveCleanForSync(s.machine, s'.machine, cache_idx, rid)
  ensures CacheSSM.Internal(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest))
  {
    assert CacheSSM.InternalStep(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest), CacheSSM.ObserveCleanForSyncStep(cache_idx, rid));
  }

  lemma ApplyRead_Monotonic(s: A.Variables, s': A.Variables, rest: CacheSSM.M,
      cache_idx: nat, rid: RequestId)
  requires Inv(A.Variables(s.disk, CacheSSM.dot(s.machine, rest)))
  requires CacheSSM.ApplyRead(s.machine, s'.machine, cache_idx, rid)
  ensures CacheSSM.Internal(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest))
  {
    var a := CacheSSM.dot(s.machine, rest);
    var b := CacheSSM.dot(s'.machine, rest);
    assert rid in a.tickets;
    assert rid !in a.stubs;
    assert rid !in rest.stubs;
    assert b.M?;

    assert CacheSSM.ApplyRead(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest), cache_idx, rid);
    assert CacheSSM.InternalStep(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest), CacheSSM.ApplyReadStep(cache_idx, rid));
  }

  lemma ApplyWrite_Monotonic(s: A.Variables, s': A.Variables, rest: CacheSSM.M,
      cache_idx: nat, rid: RequestId)
  requires Inv(A.Variables(s.disk, CacheSSM.dot(s.machine, rest)))
  requires CacheSSM.ApplyWrite(s.machine, s'.machine, cache_idx, rid)
  ensures CacheSSM.Internal(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest))
  {
    var a := CacheSSM.dot(s.machine, rest);
    var b := CacheSSM.dot(s'.machine, rest);
    assert rid in a.tickets;
    assert rid !in a.stubs;
    assert rid !in rest.stubs;
    assert b.M?;

    assert CacheSSM.ApplyWrite(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest), cache_idx, rid);
    assert CacheSSM.InternalStep(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest), CacheSSM.ApplyWriteStep(cache_idx, rid));
  }

  lemma MarkDirty_Monotonic(s: A.Variables, s': A.Variables, rest: CacheSSM.M,
      cache_idx: nat)
  requires Inv(A.Variables(s.disk, CacheSSM.dot(s.machine, rest)))
  requires CacheSSM.MarkDirty(s.machine, s'.machine, cache_idx)
  ensures CacheSSM.Internal(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest))
  {
    assert CacheSSM.MarkDirty(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest), cache_idx);
    assert CacheSSM.InternalStep(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest), CacheSSM.MarkDirtyStep(cache_idx));
  }

  lemma HavocNew_Monotonic(s: A.Variables, s': A.Variables, rest: CacheSSM.M,
      cache_idx: nat, rid: RequestId, new_data: DiskIfc.Block)
  requires Inv(A.Variables(s.disk, CacheSSM.dot(s.machine, rest)))
  requires CacheSSM.HavocNew(s.machine, s'.machine, cache_idx, rid, new_data)
  ensures CacheSSM.Internal(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest))
  {
    assert CacheSSM.HavocNew(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest), cache_idx, rid, new_data);
    assert CacheSSM.InternalStep(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest), CacheSSM.HavocNewStep(cache_idx, rid, new_data));
  }

  lemma HavocEvict_Monotonic(s: A.Variables, s': A.Variables, rest: CacheSSM.M,
      cache_idx: nat, rid: RequestId)
  requires Inv(A.Variables(s.disk, CacheSSM.dot(s.machine, rest)))
  requires CacheSSM.HavocEvict(s.machine, s'.machine, cache_idx, rid)
  ensures CacheSSM.Internal(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest))
  {
    assert CacheSSM.HavocEvict(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest), cache_idx, rid);
    assert CacheSSM.InternalStep(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest), CacheSSM.HavocEvictStep(cache_idx, rid));
  }

  lemma InternalMonotonic(s: A.Variables, s': A.Variables, rest: CacheSSM.M)
  requires Inv(A.Variables(s.disk, CacheSSM.dot(s.machine, rest)))
  requires CacheSSM.Internal(s.machine, s'.machine)
  ensures CacheSSM.Internal(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest))
  {
    var step :| CacheSSM.InternalStep(s.machine, s'.machine, step);
    match step {
      case StartReadStep(cache_idx, disk_idx) => {
        StartRead_Monotonic(s, s', rest, cache_idx, disk_idx);
      }

      case FinishReadStep(cache_idx, disk_idx) => {
        FinishRead_Monotonic(s, s', rest, cache_idx, disk_idx);
      }

      case StartWritebackStep(cache_idx) => {
        StartWriteback_Monotonic(s, s', rest, cache_idx);
      }

      case FinishWritebackStep(cache_idx) => {
        FinishWriteback_Monotonic(s, s', rest, cache_idx);
      }

      case EvictStep(cache_idx) => {
        Evict_Monotonic(s, s', rest, cache_idx);
      }

      case ObserveCleanForSyncStep(cache_idx, rid) => {
        ObserveCleanForSync_Monotonic(s, s', rest, cache_idx, rid);
      }

      case ApplyReadStep(cache_idx, rid) => {
        ApplyRead_Monotonic(s, s', rest, cache_idx, rid);
      }

      case ApplyWriteStep(cache_idx, rid) => {
        ApplyWrite_Monotonic(s, s', rest, cache_idx, rid);
      }

      case MarkDirtyStep(cache_idx) => {
        MarkDirty_Monotonic(s, s', rest, cache_idx);
      }

      case HavocNewStep(cache_idx, rid, new_data) => {
        HavocNew_Monotonic(s, s', rest, cache_idx, rid, new_data);
      }

      case HavocEvictStep(cache_idx, rid) => {
        HavocEvict_Monotonic(s, s', rest, cache_idx, rid);
      }
    }
  }

  lemma Machine_Internal_PreservesInv(s: A.Variables, s': A.Variables)
  requires Inv(s)
  requires Internal(s.machine, s'.machine)
  requires s.disk == s'.disk
  ensures Inv(s')
  {
    var step :| CacheSSM.InternalStep(s.machine, s'.machine, step);
    match step {
      case StartReadStep(cache_idx, disk_idx) =>
        StartRead_PreservesInv(s, s', cache_idx, disk_idx);

      case FinishReadStep(cache_idx, disk_idx) => 
        FinishRead_PreservesInv(s, s', cache_idx, disk_idx);

      case StartWritebackStep(cache_idx) =>
        StartWriteback_PreservesInv(s, s', cache_idx);

      case FinishWritebackStep(cache_idx) =>
        FinishWriteback_PreservesInv(s, s', cache_idx);

      case EvictStep(cache_idx) =>
        Evict_PreservesInv(s, s', cache_idx);

      case ObserveCleanForSyncStep(cache_idx, rid) =>
        ObserveCleanForSync_PreservesInv(s, s', cache_idx, rid);

      case ApplyReadStep(cache_idx, rid) =>
        ApplyRead_PreservesInv(s, s', cache_idx, rid);

      case ApplyWriteStep(cache_idx, rid) =>
        ApplyWrite_PreservesInv(s, s', cache_idx, rid);

      case MarkDirtyStep(cache_idx) =>
        MarkDirty_PreservesInv(s, s', cache_idx);

      case HavocNewStep(cache_idx, rid, new_data) =>
        HavocNew_PreservesInv(s, s', cache_idx, rid, new_data);

      case HavocEvictStep(cache_idx, rid) =>
        HavocEvict_PreservesInv(s, s', cache_idx, rid);
    }
  }

  lemma ProcessRead_PreservesInv(s: A.Variables, s': A.Variables, id: RequestId)
  requires Inv(s)
  requires AsyncDisk.ProcessRead(s.disk, s'.disk, id)
  requires s.machine == s'.machine
  ensures Inv(s')
  {
  }

  lemma ProcessWrite_PreservesInv(s: A.Variables, s': A.Variables, id: RequestId)
  requires Inv(s)
  requires AsyncDisk.ProcessWrite(s.disk, s'.disk, id)
  requires s.machine == s'.machine
  ensures Inv(s')
  {
  }

  lemma HavocConflictingWrites_PreservesInv(s: A.Variables, s': A.Variables, id: RequestId, id':RequestId)
  requires Inv(s)
  requires AsyncDisk.HavocConflictingWrites(s.disk, s'.disk, id, id')
  requires s.machine == s'.machine
  ensures Inv(s')
  {
  }

  lemma HavocConflictingWriteRead_PreservesInv(s: A.Variables, s': A.Variables, id: RequestId,id': RequestId)
  requires Inv(s)
  requires AsyncDisk.HavocConflictingWriteRead(s.disk, s'.disk, id, id')
  requires s.machine == s'.machine
  ensures Inv(s')
  {
  }

  lemma DiskInternal_PreservesInv(s: A.Variables, s': A.Variables)
  requires Inv(s)
  requires A.DiskInternal(s, s')
  ensures Inv(s')
  {
    var step :| AsyncDisk.NextInternalStep(s.disk, s'.disk, step);
    match step {
      case ProcessReadStep(id) => ProcessRead_PreservesInv(s, s', id);
      case ProcessWriteStep(id) => ProcessWrite_PreservesInv(s, s', id);
      case HavocConflictingWritesStep(id, id') => HavocConflictingWrites_PreservesInv(s, s', id, id');
      case HavocConflictingWriteReadStep(id, id') => HavocConflictingWriteRead_PreservesInv(s, s', id, id');
    }
  }

  lemma Interaction_ReqWrite_PreservesInv(s: A.Variables, s': A.Variables, dop: DiskIfc.DiskOp)
  requires Inv(s)
  requires AsyncDisk.RecvWrite(s.disk, s'.disk, dop)
  requires s.machine == CacheSSM.dot(s'.machine, CacheSSM.DiskWriteReq(dop.reqWrite.addr, dop.reqWrite.data))
  ensures Inv(s')
  {
    var x := CacheSSM.DiskWriteReq(dop.reqWrite.addr, dop.reqWrite.data);
    assert s.machine == CacheSSM.dot(s'.machine, x);

    assert s'.machine.M?;
    assert s.machine.entries == s'.machine.entries;
    assert s.machine.statuses == s'.machine.statuses;
    assert s.machine.disk_idx_to_cache_idx == s'.machine.disk_idx_to_cache_idx;
    assert s.machine.tickets == s'.machine.tickets;
    assert s.machine.stubs == s'.machine.stubs;

    assert forall i :: InverseMapConsistent(s.machine, i) ==> InverseMapConsistent(s'.machine, i);
    assert forall i :: IsReading(s.machine, i) ==> IsReading(s'.machine, i);
    assert forall i :: IsWriting(s.machine, i) ==> IsWriting(s'.machine, i);
  }

  lemma Interaction_RespWrite_PreservesInv(s: A.Variables, s': A.Variables, dop: DiskIfc.DiskOp)
  requires Inv(s)
  requires AsyncDisk.AckWrite(s.disk, s'.disk, dop)
  requires s'.machine == CacheSSM.dot(s.machine, CacheSSM.DiskWriteResp(dop.respWrite.addr))
  ensures Inv(s')
  {
    var x := CacheSSM.DiskWriteResp(dop.respWrite.addr);
    assert s'.machine == CacheSSM.dot(s.machine, x);

    assert s'.machine.M?;
    assert s.machine.entries == s'.machine.entries;
    assert s.machine.statuses == s'.machine.statuses;
    assert s.machine.disk_idx_to_cache_idx == s'.machine.disk_idx_to_cache_idx;
    assert s.machine.tickets == s'.machine.tickets;
    assert s.machine.stubs == s'.machine.stubs;

    assert forall i :: InverseMapConsistent(s.machine, i) ==> InverseMapConsistent(s'.machine, i);
    assert forall i :: IsReading(s.machine, i) ==> IsReading(s'.machine, i);
    assert forall i :: IsWriting(s.machine, i) ==> IsWriting(s'.machine, i);
  }

  lemma Interaction_ReqRead_PreservesInv(s: A.Variables, s': A.Variables, dop: DiskIfc.DiskOp)
  requires Inv(s)
  requires AsyncDisk.RecvRead(s.disk, s'.disk, dop)
  requires s.machine == CacheSSM.dot(s'.machine, CacheSSM.DiskReadReq(dop.reqRead.addr))
  ensures Inv(s')
  {
    /*assert s.machine.M?;
    assert s'.machine.M? by {
      if s'.machine == Fail {
        assert CacheSSM.dot(Fail, CacheSSM.DiskReadReq(dop.reqRead.addr)) == Fail;
        assert CacheSSM.dot(s'.machine, CacheSSM.DiskReadReq(dop.reqRead.addr)) == Fail;
        assert s.machine == Fail;
      }
    }*/

    var x := CacheSSM.DiskReadReq(dop.reqRead.addr);
    assert s.machine == CacheSSM.dot(s'.machine, x);

    assert s'.machine.M?;
    assert s.machine.entries == s'.machine.entries;
    assert s.machine.statuses == s'.machine.statuses;
    assert s.machine.disk_idx_to_cache_idx == s'.machine.disk_idx_to_cache_idx;
    assert s.machine.tickets == s'.machine.tickets;
    assert s.machine.stubs == s'.machine.stubs;

    assert forall i :: InverseMapConsistent(s.machine, i) ==> InverseMapConsistent(s'.machine, i);
    assert forall i :: IsReading(s.machine, i) ==> IsReading(s'.machine, i);
    assert forall i :: IsWriting(s.machine, i) ==> IsWriting(s'.machine, i);
  }

  lemma Interaction_RespRead_PreservesInv(s: A.Variables, s': A.Variables, dop: DiskIfc.DiskOp)
  requires Inv(s)
  requires AsyncDisk.AckRead(s.disk, s'.disk, dop)
  requires s'.machine == CacheSSM.dot(s.machine, CacheSSM.DiskReadResp(dop.respRead.addr, dop.respRead.data))
  ensures Inv(s')
  {
    var x := CacheSSM.DiskReadResp(dop.respRead.addr, dop.respRead.data);
    assert s'.machine == CacheSSM.dot(s.machine, x);

    assert s'.machine.M?;
    assert s.machine.entries == s'.machine.entries;
    assert s.machine.statuses == s'.machine.statuses;
    assert s.machine.disk_idx_to_cache_idx == s'.machine.disk_idx_to_cache_idx;
    assert s.machine.tickets == s'.machine.tickets;
    assert s.machine.stubs == s'.machine.stubs;

    assert forall i :: InverseMapConsistent(s.machine, i) ==> InverseMapConsistent(s'.machine, i);
    assert forall i :: IsReading(s.machine, i) ==> IsReading(s'.machine, i);
    assert forall i :: IsWriting(s.machine, i) ==> IsWriting(s'.machine, i);
  }

  lemma Interaction_PreservesInv(s: A.Variables, s': A.Variables, dop: DiskIfc.DiskOp)
  requires Inv(s)
  requires A.Interaction(s, s', dop)
  ensures Inv(s')
  {
    match dop {
      case ReqReadOp(id, reqRead) => {
        Interaction_ReqRead_PreservesInv(s, s', dop);
      }
      case ReqWriteOp(id, reqWrite) => {
        Interaction_ReqWrite_PreservesInv(s, s', dop);
      }
      case RespReadOp(id, respRead) => {
        Interaction_RespRead_PreservesInv(s, s', dop);
      }
      case RespWriteOp(id, respWrite) => {
        Interaction_RespWrite_PreservesInv(s, s', dop);
      }
    }
  }

  lemma Internal_PreservesInv(s: A.Variables, s': A.Variables)
  requires Inv(s)
  requires A.Internal(s, s')
  ensures Inv(s')
  {
    var step :| A.InternalStep(s, s', step);
    match step {
      case MachineStep(shard, shard', rest) => {
        InternalMonotonic(
            A.Variables(s.disk, shard),
            A.Variables(s.disk, shard'),
            rest);
        Machine_Internal_PreservesInv(s, s');
      }
      case InteractionStep(dop) => {
        Interaction_PreservesInv(s, s', dop);
      }
      case DiskInternalStep => {
        DiskInternal_PreservesInv(s, s');
      }
    }
  }

  lemma NextPreservesInv(s: A.Variables, s': A.Variables, op: ifc.Op)
  requires Inv(s)
  requires A.Next(s, s', op)
  ensures Inv(s')
  {
    match op {
      case Start(rid, input) => {
        Start_PreservesInv(s, s', rid, input);
      }
      case End(rid, output) => {
        End_PreservesInv(s, s', rid, output);
      }
      case CrashOp => {
        InitImpliesInv(s');
      }
      case InternalOp => {
        Internal_PreservesInv(s, s');
      }
    }
  }
}
