include "../../framework/DiskSSM.s.dfy"
include "CacheSpec.s.dfy"

module SimpleCacheStateMachine refines StateMachine(CrashAsyncIfc(CacheIfc)) {
  import opened NativeTypes
  import opened RequestIds
  import CacheIfc
  import DiskIfc

  datatype Entry =
    | Empty
    | Reading(disk_idx: nat)
    | Clean(disk_idx: nat, data: seq<byte>)
    | Dirty(disk_idx: nat, data: seq<byte>)
    | Writeback(disk_idx: nat, data: seq<byte>)

  datatype Variables = Variables(
    entries: imap<nat, Entry>,
    write_reqs: map<nat, seq<byte>>,
    write_resps: set<nat>,
    read_reqs: set<nat>,
    read_resps: map<nat, seq<byte>>,
    tickets: map<RequestId, CacheIfc.Input>,
    stubs: map<RequestId, CacheIfc.Output>,
    disk: imap<nat, seq<byte>>,
    sync_reqs: map<RequestId, set<nat>>,
    havocs: map<RequestId, nat>
  )

  predicate True(d: nat) { true }

  predicate Init(s: Variables) {
    && s.entries == (imap k | True(k) :: Empty)
    && s.write_reqs == map[]
    && s.write_resps == {}
    && s.read_reqs == {}
    && s.read_resps == map[]
    && s.tickets == map[]
    && s.stubs == map[]
    && (forall k: nat :: k in s.disk)
  }

  predicate StartRead(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat, disk_idx: nat) {
    && op.InternalOp?
    && cache_idx in s.entries
    && s.entries[cache_idx].Empty?
    && (forall i | i in s.entries :: !s.entries[i].Empty? ==>
          s.entries[i].disk_idx != disk_idx)
    && s' == s
      .(entries := s.entries[cache_idx := Reading(disk_idx)])
      .(read_reqs := s.read_reqs + {disk_idx})
  }

  predicate FinishRead(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat, disk_idx: nat) {
    && op.InternalOp?
    && cache_idx in s.entries
    && disk_idx in s.read_resps
    && s.entries[cache_idx].Reading?
    && s.entries[cache_idx].disk_idx == disk_idx
    && s' == s
      .(entries := s.entries[cache_idx := Clean(disk_idx, s.read_resps[disk_idx])])
      .(read_resps := s.read_resps - {disk_idx})
  }

  predicate MarkDirty(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat) {
    && op.InternalOp?
    && cache_idx in s.entries
    && s.entries[cache_idx].Clean?
    && s' == s.(entries := s.entries[cache_idx := Dirty(s.entries[cache_idx].disk_idx, s.entries[cache_idx].data)])
  }

  predicate StartWriteback(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat, disk_idx: nat) {
    && op.InternalOp?
    && cache_idx in s.entries
    && s.entries[cache_idx].Dirty?
    && s.entries[cache_idx].disk_idx == disk_idx
    && s' == s
        .(entries := s.entries[cache_idx := Writeback(s.entries[cache_idx].disk_idx, s.entries[cache_idx].data)])
        .(write_reqs := s.write_reqs[disk_idx := s.entries[cache_idx].data])
  }

  predicate FinishWriteback(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat, disk_idx: nat) {
    && op.InternalOp?
    && cache_idx in s.entries
    && s.entries[cache_idx].Writeback?
    && s.entries[cache_idx].disk_idx == disk_idx
    && disk_idx in s.write_resps
    && s' == s
        .(entries := s.entries[cache_idx := Clean(s.entries[cache_idx].disk_idx, s.entries[cache_idx].data)])
        .(write_resps := s.write_resps - {disk_idx})
  }

  predicate Evict(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat) {
    && op.InternalOp?
    && cache_idx in s.entries
    && s.entries[cache_idx].Clean?
    && s' == s
        .(entries := s.entries[cache_idx := Empty])
  }

  predicate ProcessRead(s: Variables, s': Variables, op: ifc.Op, disk_idx: nat) {
    && op.InternalOp?
    && disk_idx in s.read_reqs
    && disk_idx in s.disk
    && s' == s
        .(read_reqs := s.read_reqs - {disk_idx})
        .(read_resps := s.read_resps[disk_idx := s.disk[disk_idx]])
  }

  predicate ProcessWrite(s: Variables, s': Variables, op: ifc.Op, disk_idx: nat) {
    && op.InternalOp?
    && disk_idx in s.write_reqs
    && disk_idx in s.disk
    && s' == s
        .(write_reqs := s.write_reqs - {disk_idx})
        .(write_resps := s.write_resps + {disk_idx})
        .(disk := s.disk[disk_idx := s.write_reqs[disk_idx]])
  }

  predicate Crash(s: Variables, s': Variables, op: ifc.Op) {
    && op.CrashOp?
    && s'.entries == (imap k | True(k) :: Empty)
    && s'.write_reqs == map[]
    && s'.write_resps == {}
    && s'.read_reqs == {}
    && s'.read_resps == map[]
    && s'.tickets == map[]
    && s'.stubs == map[]
    && s'.disk == s.disk
  }

  predicate NewTicket(s: Variables, s': Variables, op: ifc.Op) {
    && op.Start?
    && (op.input.WriteInput? || op.input.ReadInput?)
    && op.rid !in s.tickets
    && s' == s.(tickets := s.tickets[op.rid := op.input])
  }

  predicate ConsumeStub(s: Variables, s': Variables, op: ifc.Op) {
    && op.End?
    && op.rid in s.stubs && s.stubs[op.rid] == op.output
    && s' == s.(stubs := s.stubs - {op.rid})
  }

  predicate NewSyncTicket(s: Variables, s': Variables, op: ifc.Op) {
    && op.Start?
    && op.input.SyncInput?
    && op.rid !in s.sync_reqs
    && s' == s.(sync_reqs := s.sync_reqs[op.rid := op.input.keys])
  }

  predicate ConsumeSyncStub(s: Variables, s': Variables, op: ifc.Op) {
    && op.End?
    && op.output.SyncOutput?
    && op.rid in s.sync_reqs
    && s.sync_reqs[op.rid] == {}
    && s' == s.(sync_reqs := s.sync_reqs - {op.rid})
  }

  predicate ObserveCleanForSync(s: Variables, s': Variables, op: ifc.Op, rid: RequestId, cache_idx: nat) {
    && op.InternalOp?
    && rid in s.sync_reqs
    && cache_idx in s.entries
    && s.entries[cache_idx].Clean?
    && s' == s.(sync_reqs := s.sync_reqs[
        rid := s.sync_reqs[rid] - {s.entries[cache_idx].disk_idx}])
  }

  predicate NewHavocTicket(s: Variables, s': Variables, op: ifc.Op) {
    && op.Start?
    && op.input.HavocInput?
    && op.rid !in s.havocs
    && s' == s.(havocs := s.havocs[op.rid := op.input.key])
  }

  predicate ConsumeHavocStub(s: Variables, s': Variables, op: ifc.Op) {
    && op.End?
    && op.output.HavocOutput?
    && op.rid in s.havocs
    && s' == s.(havocs := s.havocs - {op.rid})
  }

  predicate ApplyRead(s: Variables, s': Variables, op: ifc.Op,
      rid: RequestId, cache_idx: nat) {
    && op.InternalOp?
    && rid in s.tickets
    && s.tickets[rid].ReadInput?
    && cache_idx in s.entries
    && (s.entries[cache_idx].Clean? || s.entries[cache_idx].Dirty?
        || s.entries[cache_idx].Writeback?)
    && s.entries[cache_idx].disk_idx == s.tickets[rid].key
    && s' == s
      .(tickets := s.tickets - {rid})
      .(stubs := s.stubs[rid := CacheIfc.ReadOutput(s.entries[cache_idx].data)])
  }

  predicate ApplyWrite(s: Variables, s': Variables, op: ifc.Op,
      rid: RequestId, cache_idx: nat) {
    && op.InternalOp?
    && rid in s.tickets
    && s.tickets[rid].WriteInput?
    && cache_idx in s.entries
    && s.entries[cache_idx].Dirty? // can only write if it's marked dirty
    && s.entries[cache_idx].disk_idx == s.tickets[rid].key
    && s' == s
      .(tickets := s.tickets - {rid})
      .(stubs := s.stubs[rid := CacheIfc.WriteOutput])
      .(entries := s.entries[cache_idx :=
          Dirty(s.entries[cache_idx].disk_idx, s.tickets[rid].data)])
  }

  predicate HavocNew(s: Variables, s': Variables, op: ifc.Op,
      cache_idx: nat, rid: RequestId, new_data: DiskIfc.Block)
  {
    && op.InternalOp?
    && cache_idx in s.entries
    && s.entries[cache_idx] == Empty
    && rid in s.havocs
    && (forall i | i in s.entries :: !s.entries[i].Empty? ==>
          s.entries[i].disk_idx != s.havocs[rid])
    && s' == s
      .(entries := s.entries[cache_idx := Dirty(s.havocs[rid], new_data)])
  }

  predicate HavocEvict(s: Variables, s': Variables, op: ifc.Op,
      cache_idx: nat, rid: RequestId)
  {
    && op.InternalOp?
    && cache_idx in s.entries
    && (s.entries[cache_idx].Clean? || s.entries[cache_idx].Dirty?)
    && rid in s.havocs
    && s.entries[cache_idx].disk_idx == s.havocs[rid]
    && s' == s
      .(entries := s.entries[cache_idx := Empty])
  }
  
  datatype Step =
     | StartRead_Step(cache_idx: nat, disk_idx: nat)
     | FinishRead_Step(cache_idx: nat, disk_idx: nat) 
     | MarkDirty_Step(cache_idx: nat) 
     | StartWriteback_Step(cache_idx: nat, disk_idx: nat) 
     | FinishWriteback_Step(cache_idx: nat, disk_idx: nat) 
     | Evict_Step(cache_idx: nat) 
     | ProcessRead_Step(disk_idx: nat) 
     | ProcessWrite_Step(disk_idx: nat) 
     | Crash_Step
     | NewTicket_Step
     | ConsumeStub_Step
     | NewSyncTicket_Step
     | ConsumeSyncStub_Step
     | NewHavocTicket_Step
     | ConsumeHavocStub_Step
     | ObserveCleanForSync_Step(rid: RequestId, cache_idx: nat)
     | ApplyRead_Step(rid: RequestId, cache_idx: nat) 
     | ApplyWrite_Step(rid: RequestId, cache_idx: nat) 
     | HavocNew_Step(cache_idx: nat, rid: RequestId, block: DiskIfc.Block)
     | HavocEvict_Step(cache_idx: nat, rid: RequestId) 
     | Stutter_Step

  predicate NextStep(s: Variables, s': Variables, op: ifc.Op, step: Step) {
    match step {
       case StartRead_Step(cache_idx, disk_idx) => StartRead(s, s', op, cache_idx, disk_idx)
       case FinishRead_Step(cache_idx, disk_idx) => FinishRead(s, s', op, cache_idx, disk_idx)
       case MarkDirty_Step(cache_idx) => MarkDirty(s, s', op, cache_idx)
       case StartWriteback_Step(cache_idx, disk_idx) => StartWriteback(
          s, s', op, cache_idx, disk_idx)
       case FinishWriteback_Step(cache_idx, disk_idx) => FinishWriteback(
          s, s', op, cache_idx, disk_idx) 
       case Evict_Step(cache_idx) => Evict(s, s', op, cache_idx)
       case ProcessRead_Step(disk_idx) => ProcessRead(s, s', op, disk_idx)
       case ProcessWrite_Step(disk_idx) => ProcessWrite(s, s', op, disk_idx)
       case Crash_Step => Crash(s, s', op)
       case NewTicket_Step => NewTicket(s, s', op)
       case ConsumeStub_Step => ConsumeStub(s, s', op)
       case NewSyncTicket_Step => NewSyncTicket(s, s', op)
       case ConsumeSyncStub_Step => ConsumeSyncStub(s, s', op)
       case NewHavocTicket_Step => NewHavocTicket(s, s', op)
       case ConsumeHavocStub_Step => ConsumeHavocStub(s, s', op)
       case ObserveCleanForSync_Step(rid, cache_idx) =>
          ObserveCleanForSync(s, s', op, rid, cache_idx)
       case ApplyRead_Step(rid, cache_idx) => ApplyRead(s, s', op, rid, cache_idx)
       case ApplyWrite_Step(rid, cache_idx) => ApplyWrite(s, s', op, rid, cache_idx)
       case HavocNew_Step(cache_idx, rid, block) => HavocNew(s, s', op, cache_idx, rid, block)
       case HavocEvict_Step(cache_idx, rid) => HavocEvict(s, s', op, cache_idx, rid)
       case Stutter_Step => s == s' && op.InternalOp?
    }
  }

  predicate Next(s: Variables, s': Variables, op: ifc.Op) {
    exists step :: NextStep(s, s', op, step)
  }
}
