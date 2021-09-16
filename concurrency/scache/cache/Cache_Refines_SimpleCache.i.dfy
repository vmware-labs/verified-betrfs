include "SimpleCacheSM.i.dfy"
include "CacheSM.i.dfy"
include "../Constants.i.dfy"

module DiskSSM_Refines_SimpleCachine
  refines Refinement(CrashAsyncIfc(CacheIfc),
        AsyncDiskSystemStateMachine(CacheIfc, CacheSSM),
        SimpleCacheStateMachine)
{
  import opened Constants
  import opened RequestIds
  import opened Options
  import opened CacheSSM
  import CacheIfc
  import DiskIfc

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

    && s.machine.read_reqs !! s.machine.read_resps.Keys
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
    && (forall rid1 | rid1 in s.disk.reqWrites :: s.disk.reqWrites[rid1].addr !in s.machine.write_reqs)
    && (forall rid1 | rid1 in s.disk.reqWrites :: s.disk.reqWrites[rid1].addr !in s.machine.write_resps)
    && (forall rid2 | rid2 in s.disk.respWrites :: s.disk.respWrites[rid2].addr !in s.machine.write_reqs)
    && (forall rid2 | rid2 in s.disk.respWrites :: s.disk.respWrites[rid2].addr !in s.machine.write_resps)
    && (forall rid1 | rid1 in s.disk.reqWrites :: IsWriting(s.machine, s.disk.reqWrites[rid1].addr))
    && (forall rid2 | rid2 in s.disk.respWrites :: IsWriting(s.machine, s.disk.respWrites[rid2].addr))
    && (forall addr | addr in s.machine.write_reqs :: IsWriting(s.machine, addr))
    && (forall addr | addr in s.machine.write_resps :: IsWriting(s.machine, addr))
  }

  lemma InitImpliesInv(s: A.Variables)
  //requires A.Init(s)
  ensures Inv(s)
  {
  }

  lemma Start_PreservesInv(s: A.Variables, s': A.Variables, rid: RequestId, input: CacheIfc.Input)
  requires Inv(s)
  requires A.NewTicket(s, s', rid, input)
  ensures Inv(s')
  {
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
    assert s'.machine.entries == s.machine.entries;
    assert s'.machine.statuses == s.machine.statuses;

    assert forall i :: InverseMapConsistent(s.machine, i) ==> InverseMapConsistent(s'.machine, i);
    assert forall i :: IsReading(s.machine, i) ==> IsReading(s'.machine, i);
    assert forall i :: IsWriting(s.machine, i) ==> IsWriting(s'.machine, i);
  }

  lemma StartRead_PreservesInv(s: A.Variables, s': A.Variables, cache_idx: nat, disk_idx: nat)
  requires Inv(s)
  requires CacheSSM.StartRead(s.machine, s'.machine, cache_idx, disk_idx)
  requires s'.disk == s.disk
  ensures Inv(s')

  lemma FinishRead_PreservesInv(s: A.Variables, s': A.Variables, cache_idx: nat, disk_idx: nat)
  requires Inv(s)
  requires CacheSSM.FinishRead(s.machine, s'.machine, cache_idx, disk_idx)
  requires s'.disk == s.disk
  ensures Inv(s')

  lemma StartWriteback_PreservesInv(s: A.Variables, s': A.Variables, cache_idx: nat)
  requires Inv(s)
  requires CacheSSM.StartWriteback(s.machine, s'.machine, cache_idx)
  requires s'.disk == s.disk
  ensures Inv(s')

  lemma FinishWriteback_PreservesInv(s: A.Variables, s': A.Variables, cache_idx: nat)
  requires Inv(s)
  requires CacheSSM.FinishWriteback(s.machine, s'.machine, cache_idx)
  requires s'.disk == s.disk
  ensures Inv(s')

  lemma Evict_PreservesInv(s: A.Variables, s': A.Variables, cache_idx: nat, disk_idx: nat, data: DiskIfc.Block, cache_idx2_opt: Option<nat>)
  requires Inv(s)
  requires CacheSSM.Evict(s.machine, s'.machine, cache_idx, disk_idx, data, cache_idx2_opt)
  requires s'.disk == s.disk
  ensures Inv(s')

  lemma ObserveCleanForSync_PreservesInv(s: A.Variables, s': A.Variables, cache_idx: nat, disk_idx: nat, data: DiskIfc.Block, rid: RequestId, se: set<nat>)
  requires Inv(s)
  requires CacheSSM.ObserveCleanForSync(s.machine, s'.machine, cache_idx, disk_idx, data, rid, se)
  requires s'.disk == s.disk
  ensures Inv(s')

  lemma ApplyRead_PreservesInv(s: A.Variables, s': A.Variables, cache_idx: nat, disk_idx: nat, data: DiskIfc.Block, rid: RequestId)
  requires Inv(s)
  requires CacheSSM.ApplyRead(s.machine, s'.machine, cache_idx, disk_idx, data, rid)
  requires s'.disk == s.disk
  ensures Inv(s')

  lemma ApplyWrite_PreservesInv(s: A.Variables, s': A.Variables, cache_idx: nat, disk_idx: nat, data: DiskIfc.Block, new_data: DiskIfc.Block, rid: RequestId)
  requires Inv(s)
  requires CacheSSM.ApplyWrite(s.machine, s'.machine, cache_idx, disk_idx, data, new_data, rid)
  requires s'.disk == s.disk
  ensures Inv(s')

  lemma MarkDirty_PreservesInv(s: A.Variables, s': A.Variables, cache_idx: nat)
  requires Inv(s)
  requires CacheSSM.MarkDirty(s.machine, s'.machine, cache_idx)
  requires s'.disk == s.disk
  ensures Inv(s')

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
        assume false;
        assert CacheSSM.InternalStep(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest), step);
      }

      case StartWritebackStep(cache_idx) => {
        assume false;
        assert CacheSSM.Internal(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest));
      }

      case FinishWritebackStep(cache_idx) => {
        assume false;
        assert CacheSSM.Internal(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest));
      }

      case EvictStep(cache_idx, disk_idx, data, cache_idx2_opt) => {
        assume false;
        assert CacheSSM.Internal(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest));
      }

      case ObserveCleanForSyncStep(cache_idx, disk_idx, data, rid, se) => {
        assume false;
        assert CacheSSM.Internal(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest));
      }

      case ApplyReadStep(cache_idx, disk_idx, data, rid) => {
        assume false;
        assert CacheSSM.Internal(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest));
      }

      case ApplyWriteStep(cache_idx, disk_idx, data, new_data, rid) => {
        assume false;
        assert CacheSSM.Internal(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest));
      }

      case MarkDirtyStep(cache_idx) => {
        assume false;
        assert CacheSSM.Internal(CacheSSM.dot(s.machine, rest), CacheSSM.dot(s'.machine, rest));
      }
    }
  }

/*
  lemma Internal_PreservesInv(s: A.Variables, s': A.Variables)
  requires Inv(s)
  requires A.Machine(s, s')
  ensures Inv(s')
  {
    var step :| CacheSSM.InternalStep(s.machine, s'.machine, step);
    match step {
      case StartReadStep(cache_idx, disk_idx) =>
        StartRead_PreservesInv(s, s', cache_idx, disk_idx);

      case FinishReadStep(cache_idx, disk_idx) => 
        FinishRead_PreservesInv(s, s', cache_idx, disk_idx);

      case StartWritebackStep(cache_idx, disk_idx, data) =>
        StartWriteback_PreservesInv(s, s', cache_idx, disk_idx, data);

      case FinishWritebackStep(cache_idx, disk_idx, data) =>
        FinishWriteback_PreservesInv(s, s', cache_idx, disk_idx, data);

      case EvictStep(cache_idx, disk_idx, data, cache_idx2_opt) =>
        Evict_PreservesInv(s, s', cache_idx, disk_idx, data, cache_idx2_opt);

      case ObserveCleanForSyncStep(cache_idx, disk_idx, data, rid, se) =>
        ObserveCleanForSync_PreservesInv(s, s', cache_idx, disk_idx, data, rid, se);

      case ApplyReadStep(cache_idx, disk_idx, data, rid) =>
        ApplyRead_PreservesInv(s, s', cache_idx, disk_idx, data, rid);

      case ApplyWriteStep(cache_idx, disk_idx, data, new_data, rid) =>
        ApplyWrite_PreservesInv(s, s', cache_idx, disk_idx, data, new_data, rid);

      case MarkDirtyStep(cache_idx) =>
        MarkDirty_PreservesInv(s, s', cache_idx);
    }
  }
  */

  lemma NextPreservesInv(s: A.Variables, s': A.Variables, op: ifc.Op)
  //requires Inv(s)
  //requires A.Next(s, s', op)
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
        assume false;
        //Internal_PreservesInv(s, s');
      }
    }
  }

  function I(s: A.Variables) : B.Variables
  //requires Inv(s)

  lemma InitRefinesInit(s: A.Variables)
  //requires A.Init(s)
  //requires Inv(s)
  ensures B.Init(I(s))
  {
  }

  lemma NextRefinesNext(s: A.Variables, s': A.Variables, op: ifc.Op)
  //requires Inv(s)
  //requires Inv(s')
  //requires A.Next(s, s', op)
  ensures B.Next(I(s), I(s'), op)
  {
  }

}
