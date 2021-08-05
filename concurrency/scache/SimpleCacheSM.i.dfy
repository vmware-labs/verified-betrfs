include "../framework/DiskSSM.s.dfy"
include "CacheTypes.i.dfy"

module SimpleCacheStateMachine refines StateMachine(CrashAsyncIfc(CacheIfc)) {
  import opened CacheTypes

  datatype Entry =
    | Empty
    | Reading(disk_idx: nat)
    | Full(disk_idx: nat, data: seq<byte>)
    | Dirty(disk_idx: nat, data: seq<byte>)
    | Writeback(disk_idx: nat, data: seq<byte>)
  )

  datatype Variables = Variables(
    entries: map<nat, Entry>,
    write_reqs: map<nat, seq<byte>>,
    write_resps: set<nat>,
    read_reqs: set<nat>,
    read_resps: map<nat, seq<byte>>,
    tickets: map<RequestId, IOIfc.Input>,
    stubs: map<RequestId, IOIfc.Output>
    disk: map<nat, seq<byte>>
  )

  predicate StartRead(s: Variables, s': Variables, op: IOIfc.Op, cache_idx: nat, disk_idx: nat) {
    && op.InternalOp?
    && cache_idx in s.entries
    && s.entries[cache_idx].Empty?
    && (forall i | i in entries :: entries[i].status != Empty ==>
          entries[i].disk_idx != disk_idx)
    && s' == s
      .(entries := s.entries[cache_idx := Reading(disk_idx)])
      .(read_reqs := s.read_reqs + {disk_idx})
  }

  predicate FinishRead(s: Variables, s': Variables, op: IOIfc.Op, cache_idx: nat, disk_idx: nat) {
    && op.InternalOp?
    && cache_idx in s.entries
    && disk_idx in s.read_resps
    && s.entries[cache_idx].Reading?
    && s.entries[cache_idx].disk_idx == disk_idx
    && s' == s
      .(entries := s.entries[cache_idx := Clean(disk_idx, s.read_resps[disk_idx].data)])
      .(read_resps := s.read_resps - {disk_idx})
  }

  predicate MakeDirty(s: Variables, s': Variables, op: IOIfc.Op, cache_idx: nat) {
    && op.InternalOp?
    && cache_idx in s.entries
    && s.entries[cache_idx].Clean?
    && s' == s.(entries := s.entries[cache_idx := Dirty(s.entries[cache_idx].disk_idx, s.entries[cache_idx].data))
  }

  predicate StartWriteback(s: Variables, s': Variables, op: IOIfc.Op, cache_idx: nat, disk_idx: nat) {
    && op.InternalOp?
    && cache_idx in s.entries
    && s.entries[cache_idx].Dirty?
    && s.entries[cache_idx].disk_idx == disk_idx
    && s' == s
        .(entries := s.entries[cache_idx] := Writeback(s.entries[cache_idx].disk_idx, s.entries[cache_idx].data))
        .(write_reqs := s.write_reqs[disk_idx := s.entries[cache_idx].data])
  }

  predicate FinishWriteback(s: Variables, s': Variables, op: IOIfc.Op, cache_idx: nat, disk_idx: nat) {
    && op.InternalOp?
    && cache_idx in s.entries
    && s.entries[cache_idx].Writeback?
    && s.entries[cache_idx].disk_idx == disk_idx
    && s' == s
        .(entries := s.entries[cache_idx] := Clean(s.entries[cache_idx].disk_idx, s.entries[cache_idx].data))
        .(write_resps := s.write_resps - {disk_idx})
  }

  predicate Evict(s: Variables, s': Variables, op: IOIfc.Op, cache_idx: nat) {
    && op.InternalOp?
    && cache_idx in s.entries
    && s.entries[cache_idx].Clean?
    && s' == s
        .(entries := s.entries[cache_idx := Empty])
  }

  predicate ProcessRead(s: Variables, s': Variables, op: IOIfc.Op, disk_idx: nat) {
    && op.InternalOp?
    && disk_idx in s.read_reqs
    && disk_idx in s.disk
    && s' == s
        .(read_reqs := s.read_reqs - {disk_idx})
        .(read_resps := s.read_resps[disk_idx := s.disk[disk_idx]])
  }

  predicate ProcessWrite(s: Variables, s': Variables, op: IOIfc.Op, disk_idx: nat) {
    && op.InternalOp?
    && disk_idx in s.write_reqs
    && s' == s
        .(write_reqs := s.write_reqs - {disk_idx})
        .(write_resps := s.write_resps[disk_idx + {disk_idx}])
        .(disk := s.disk[disk_idx := s.write_reqs[disk_idx].data])
  }

  predicate Crash(s: Variables, s': Variables, op: IOIfc.Op) {
  }
}
