include "../../framework/DiskSSM.s.dfy"
include "CacheSpec.s.dfy"
include "../Constants.i.dfy"
include "../../../lib/Base/Option.s.dfy"

module CacheStatusType {
  datatype Status = //Empty | Reading |
        Clean | Dirty | Writeback
}

module CacheSSM refines DiskSSM(CacheIfc) {
  import opened Options
  import CacheIfc
  import opened CacheStatusType
  import opened Constants

  datatype Entry =
    | Empty
    | Reading(ghost disk_idx: nat)
    | Entry(ghost disk_idx: nat, data: DiskIfc.Block)

  // Notes:
  //
  //  - Entry is separate from Status because there are some cases
  //    where we need to have shared access to the Entry while modifying
  //    the Status.
  //
  //  - The `disk_idx_to_cache_idx` map is an inverse map from the
  //    cache_idx -> disk_idx map implicit in the `entries`.
  //    Having this map serves two purposes:
  //
  //    * One, it lets the implementation find the corresponding cache_idx
  //      given a disk_idx, although in some sense this is just an implementation
  //      detail, not very relevant to the state machine.
  //
  //    * Two, it lets us enforce an invariant that, for any single disk_idx,
  //      there is only one cache_idx that maps to it.

  datatype M = M(
    ghost disk_idx_to_cache_idx: map<nat, Option<nat>>,
    ghost entries: map<nat, Entry>,
    ghost statuses: map<nat, Status>,
    ghost write_reqs: map<nat, DiskIfc.Block>,
    ghost write_resps: set<nat>,
    ghost read_reqs: set<nat>,
    ghost read_resps: map<nat, DiskIfc.Block>,
    ghost tickets: map<RequestId, IOIfc.Input>,
    ghost stubs: map<RequestId, IOIfc.Output>,
    ghost sync_reqs: map<RequestId, set<nat>>,
    ghost havocs: map<RequestId, nat>
  ) | Fail

  function union_map<K, V>(m1: map<K, V>, m2: map<K, V>) : map<K, V> {
    map k | k in m1.Keys + m2.Keys :: if k in m1 then m1[k] else m2[k]
  }

  function dot(x: M, y: M) : M {
    if x.M? && y.M?
        && x.disk_idx_to_cache_idx.Keys !! y.disk_idx_to_cache_idx.Keys
        && x.entries.Keys !! y.entries.Keys
        && x.statuses.Keys !! y.statuses.Keys
        && x.write_reqs.Keys !! y.write_reqs.Keys
        && x.write_resps !! y.write_resps
        && x.read_reqs !! y.read_reqs
        && x.read_resps.Keys !! y.read_resps.Keys
        && x.tickets.Keys !! y.tickets.Keys
        && x.stubs.Keys !! y.stubs.Keys
        && x.sync_reqs.Keys !! y.sync_reqs.Keys
        && x.havocs.Keys !! y.havocs.Keys
    then
      M(
        union_map(x.disk_idx_to_cache_idx, y.disk_idx_to_cache_idx),
        union_map(x.entries, y.entries),
        union_map(x.statuses, y.statuses),
        union_map(x.write_reqs, y.write_reqs),
        x.write_resps + y.write_resps,
        x.read_reqs + y.read_reqs,
        union_map(x.read_resps, y.read_resps),
        union_map(x.tickets, y.tickets),
        union_map(x.stubs, y.stubs),
        union_map(x.sync_reqs, y.sync_reqs),
        union_map(x.havocs, y.havocs)
      )
    else
      Fail
  }

  function DiskIdxToCacheIdx(disk_idx: nat, cache_idx: Option<nat>) : M {
    M(map[disk_idx := cache_idx],
      map[], map[], map[], {}, {}, map[], map[], map[], map[], map[])
  }

  function CacheEntry(cache_idx: nat, disk_idx: nat, data: DiskIfc.Block) : M {
    M(map[],
      map[cache_idx := Entry(disk_idx, data)],
      map[], map[], {}, {}, map[], map[], map[], map[], map[])
  }

  function CacheReading(cache_idx: nat, disk_idx: nat) : M {
    M(map[],
      map[cache_idx := Reading(disk_idx)],
      map[], map[], {}, {}, map[], map[], map[], map[], map[])
  }

  function CacheEmpty(cache_idx: nat) : M {
    M(map[],
      map[cache_idx := Empty],
      map[], map[], {}, {}, map[], map[], map[], map[], map[])
  }

  function CacheStatus(cache_idx: nat, status: Status) : M {
    M(map[], map[],
      map[cache_idx := status],
      map[], {}, {}, map[], map[], map[], map[], map[])
  }

  function DiskWriteReq(disk_addr: nat, data: DiskIfc.Block) : M {
    M(map[], map[], map[],
      map[disk_addr := data],
      {}, {}, map[], map[], map[], map[], map[])
  }

  function DiskWriteResp(disk_addr: nat) : M {
    M(map[], map[], map[], map[],
      {disk_addr},
      {}, map[], map[], map[], map[], map[])
  }

  function DiskReadReq(disk_addr: nat) : M {
    M(map[], map[], map[], map[], {},
      {disk_addr},
      map[], map[], map[], map[], map[])
  }

  function DiskReadResp(disk_addr: nat, data: DiskIfc.Block) : M {
    M(map[], map[], map[], map[], {}, {},
      map[disk_addr := data],
      map[], map[], map[], map[])
  }

  function NormalTicket(rid: RequestId, input: IOIfc.Input) : M {
    M(map[], map[], map[], map[], {}, {}, map[],
      map[rid := input],
      map[], map[], map[])
  }

  function NormalStub(rid: RequestId, output: IOIfc.Output) : M {
    M(map[], map[], map[], map[], {}, {}, map[], map[],
      map[rid := output],
      map[], map[])
  }

  function SyncReq(rid: RequestId, disk_indices: set<nat>) : M {
    M(map[], map[], map[], map[], {}, {}, map[], map[], map[],
      map[rid := disk_indices], map[])
  }

  function Havoc(rid: RequestId, disk_idx: nat) : M {
    M(map[], map[], map[], map[], {}, {}, map[], map[], map[],
      map[], map[rid := disk_idx])
  }

  function unit() : M {
    M(map[], map[], map[], map[], {}, {}, map[], map[], map[], map[], map[])
  }

  function Ticket(rid: RequestId, input: IOIfc.Input) : M {
    if input.SyncInput? then
      SyncReq(rid, input.keys)
    else if input.HavocInput? then
      Havoc(rid, input.key)
    else
      NormalTicket(rid, input)
  }

  function Stub(rid: RequestId, output: IOIfc.Output) : M {
    if output.SyncOutput? then
      SyncReq(rid, {})
    else if output.HavocOutput? then
      Havoc(rid, output.key)
    else
      NormalStub(rid, output)
  }

  // By returning a set of request ids "in use", we enforce that
  // there are only a finite number of them (i.e., it is always possible to find
  // a free one).
  function request_ids_in_use(m: M) : set<RequestId> {
    if m.M? then
      m.tickets.Keys + m.stubs.Keys + m.sync_reqs.Keys + m.havocs.Keys
    else
      {}
  }

  predicate Init(s: M)
  {
    && s == M(
      (map i: nat | 0 <= i < NUM_DISK_PAGES as nat :: None),
      (map i: nat | 0 <= i < CACHE_SIZE as nat :: Empty),
       map[], map[], {}, {},
       map[], map[], map[], map[], map[])
  }

  function dot3(a: M, b: M, c: M) : M {
    dot(dot(a, b), c)
  }

  function dot4(a: M, b: M, c: M, d: M) : M {
    dot(dot(dot(a, b), c), d)
  }

  predicate StartRead(s: M, s': M,
      cache_idx: nat, disk_idx: nat) {
    && s.M?
    && cache_idx in s.entries
    && s.entries[cache_idx] == Empty
    && disk_idx in s.disk_idx_to_cache_idx
    && s.disk_idx_to_cache_idx[disk_idx] == None
    && s' == s
      .(entries := s.entries[cache_idx := Reading(disk_idx)])
      .(disk_idx_to_cache_idx := s.disk_idx_to_cache_idx[disk_idx := Some(cache_idx)])
      .(read_reqs := s.read_reqs + {disk_idx})
      /*
    && shard == dot(
        CacheEmpty(cache_idx),
        DiskIdxToCacheIdx(disk_idx, None)
       )
    && shard' == dot3(
        CacheReading(cache_idx, disk_idx),
        DiskIdxToCacheIdx(disk_idx, Some(cache_idx)),
        DiskReadReq(disk_idx)
       )
       */
  }

  predicate FinishRead(s: M, s': M, cache_idx: nat, disk_idx: nat)
  {
    && s.M?
    && cache_idx in s.entries
    && s.entries[cache_idx] == Reading(disk_idx)
    && disk_idx in s.read_resps
    && s' == s
      .(entries := s.entries[cache_idx := Entry(disk_idx, s.read_resps[disk_idx])])
      .(statuses := s.statuses[cache_idx := Clean])
      .(read_resps := s.read_resps - {disk_idx})
      /*
    && shard == dot(
        CacheReading(cache_idx, disk_idx),
        DiskReadResp(disk_idx, data)
       )
    && shard' == dot(
        CacheStatus(cache_idx, Clean),
        CacheEntry(cache_idx, disk_idx, data)
       )
       */
  }

  predicate StartWriteback(s: M, s': M,
      cache_idx: nat)
  {
    && s.M?
    && cache_idx in s.statuses
    && s.statuses[cache_idx] == Dirty
    && cache_idx in s.entries
    && s.entries[cache_idx].Entry?
    && s' == s
      .(statuses := s.statuses[cache_idx := Writeback])
      .(write_reqs := s.write_reqs[s.entries[cache_idx].disk_idx := s.entries[cache_idx].data])

      /*
    && shard == dot(
        CacheStatus(cache_idx, Dirty),
        CacheEntry(cache_idx, disk_idx, data)
       )
    && shard' == dot3(
        CacheStatus(cache_idx, Writeback),
        CacheEntry(cache_idx, disk_idx, data), // unchanged
        DiskWriteReq(disk_idx, data)
       )
       */
  }

  predicate FinishWriteback(s: M, s': M,
      cache_idx: nat)
  {
    && s.M?
    && cache_idx in s.entries
    && cache_idx in s.statuses
    && s.entries[cache_idx].Entry?
    && s.entries[cache_idx].disk_idx in s.write_resps
    && s' == s
        .(statuses := s.statuses[cache_idx := Clean])
        .(write_resps := s.write_resps - {s.entries[cache_idx].disk_idx})
  /*
    && shard == dot3(
        CacheEntry(cache_idx, disk_idx, data),
        CacheStatus(cache_idx, Writeback),
        DiskWriteResp(disk_idx)
       )
    && shard' == dot(
        CacheEntry(cache_idx, disk_idx, data), // unchanged
        CacheStatus(cache_idx, Clean)
      )
      */
  }

  predicate Evict(s: M, s': M,
      cache_idx: nat) {
    && s.M?
    && cache_idx in s.statuses
    && cache_idx in s.entries
    && s.statuses[cache_idx] == Clean
    && s.entries[cache_idx].Entry?
    && s.entries[cache_idx].disk_idx in s.disk_idx_to_cache_idx
    && s' == s
        .(entries := s.entries[cache_idx := Empty])
        .(disk_idx_to_cache_idx := s.disk_idx_to_cache_idx[s.entries[cache_idx].disk_idx := None])
        .(statuses := s.statuses - {cache_idx})
  /*
    && shard == dot3(
        CacheStatus(cache_idx, Clean),
        CacheEntry(cache_idx, disk_idx, data),
        DiskIdxToCacheIdx(disk_idx, cache_idx2)
      )
    && shard == dot(
        CacheEmpty(cache_idx),
        DiskIdxToCacheIdx(disk_idx, None)
      )
      */
  }

  predicate ObserveCleanForSync(s: M, s': M, cache_idx: nat, rid: RequestId)
  {
    && s.M?
    && cache_idx in s.statuses
    && cache_idx in s.entries
    && s.statuses[cache_idx] == Clean
    && s.entries[cache_idx].Entry?
    && rid in s.sync_reqs

    && s' == s.(sync_reqs :=
        s.sync_reqs[rid := s.sync_reqs[rid] - {s.entries[cache_idx].disk_idx}])

    /*
    && shard == dot3(
      CacheStatus(cache_idx, Clean),
      CacheEntry(cache_idx, disk_idx, data),
      SyncReq(rid, s)
    )
    && shard' == dot3(
      CacheStatus(cache_idx, Clean),
      CacheEntry(cache_idx, disk_idx, data),
      SyncReq(rid, s - {disk_idx})
    )
    */
  }

  predicate ApplyRead(s: M, s': M,
      cache_idx: nat, rid: RequestId)
  {
    && s.M?
    && cache_idx in s.entries
    && s.entries[cache_idx].Entry?
    && rid in s.tickets
    && s.tickets[rid].ReadInput?
    && s.tickets[rid].key == s.entries[cache_idx].disk_idx
    && s' == s
      .(tickets := s.tickets - {rid})
      .(stubs := s.stubs[rid := CacheIfc.ReadOutput(s.entries[cache_idx].data)])
    /*
    && shard == dot(
      CacheEntry(cache_idx, disk_idx, data),
      NormalTicket(rid, CacheIfc.ReadInput(disk_idx))
    )
    && shard' == dot(
      CacheEntry(cache_idx, disk_idx, data),
      NormalStub(rid, CacheIfc.ReadOutput(data))
    )
    */
  }

  predicate ApplyWrite(s: M, s': M,
      cache_idx: nat, rid: RequestId)
  {
    && s.M?
    && cache_idx in s.entries
    && cache_idx in s.statuses
    && s.entries[cache_idx].Entry?
    && s.statuses[cache_idx].Dirty?
    && rid in s.tickets
    && s.tickets[rid].WriteInput?
    && s.tickets[rid].key == s.entries[cache_idx].disk_idx
    && |s.tickets[rid].data| == 4096
    && s' == s
      .(tickets := s.tickets - {rid})
      .(stubs := s.stubs[rid := CacheIfc.WriteOutput])
      .(entries := s.entries[cache_idx :=
          Entry(s.entries[cache_idx].disk_idx, s.tickets[rid].data)])
    /*
    && shard == dot(
      CacheEntry(cache_idx, disk_idx, data),
      NormalTicket(rid, CacheIfc.WriteInput(disk_idx, new_data))
    )
    && shard' == dot(
      CacheEntry(cache_idx, disk_idx, new_data),
      NormalStub(rid, CacheIfc.WriteOutput)
    )
    */
  }

  predicate MarkDirty(s: M, s': M, cache_idx: nat)
  {
    && s.M?
    && cache_idx in s.statuses
    && s.statuses[cache_idx] == Clean
    && s' == s.(statuses := s.statuses[cache_idx := Dirty])
    /*
    && shard == CacheStatus(cache_idx, Clean)
    && shard' == CacheStatus(cache_idx, Dirty)
    */
  }

  predicate HavocNew(s: M, s': M, cache_idx: nat, rid: RequestId, new_data: DiskIfc.Block)
  {
    && s.M?
    && cache_idx in s.entries
    && s.entries[cache_idx] == Empty
    && rid in s.havocs
    && s.havocs[rid] in s.disk_idx_to_cache_idx
    && s.disk_idx_to_cache_idx[s.havocs[rid]] == None
    && s' == s
      .(entries := s.entries[cache_idx := Entry(s.havocs[rid], new_data)])
      .(statuses := s.statuses[cache_idx := Clean])
      .(disk_idx_to_cache_idx := s.disk_idx_to_cache_idx[s.havocs[rid] := Some(cache_idx)])
  }

  predicate HavocEvict(s: M, s': M, cache_idx: nat, rid: RequestId)
  {
    && s.M?
    && cache_idx in s.entries
    && s.entries[cache_idx].Entry?
    && cache_idx in s.statuses
    && rid in s.havocs
    && s.havocs[rid] in s.disk_idx_to_cache_idx
    && s' == s
      .(entries := s.entries[cache_idx := Empty])
      .(statuses := s.statuses - {cache_idx})
      .(disk_idx_to_cache_idx := s.disk_idx_to_cache_idx[s.havocs[rid] := None])
  }

  datatype Step =
    | StartReadStep(ghost cache_idx: nat, ghost disk_idx: nat)
    | FinishReadStep(ghost cache_idx: nat, ghost disk_idx: nat)
    | StartWritebackStep(ghost cache_idx: nat)
    | FinishWritebackStep(ghost cache_idx: nat)
    | EvictStep(ghost cache_idx: nat)
    | ObserveCleanForSyncStep(ghost cache_idx: nat, ghost rid: RequestId)
    | ApplyReadStep(ghost cache_idx: nat, ghost rid: RequestId)
    | ApplyWriteStep(ghost cache_idx: nat, ghost rid: RequestId)
    | MarkDirtyStep(ghost cache_idx: nat)
    | HavocNewStep(ghost cache_idx: nat, ghost rid: RequestId, ghost new_data: DiskIfc.Block)
    | HavocEvictStep(ghost cache_idx: nat, ghost rid: RequestId)

  predicate InternalStep(shard: M, shard': M, step: Step)
  {
    match step {
      case StartReadStep(cache_idx, disk_idx) =>
        StartRead(shard, shard', cache_idx, disk_idx)

      case FinishReadStep(cache_idx, disk_idx) => 
        FinishRead(shard, shard', cache_idx, disk_idx)

      case StartWritebackStep(cache_idx) =>
        StartWriteback(shard, shard', cache_idx)

      case FinishWritebackStep(cache_idx) =>
        FinishWriteback(shard, shard', cache_idx)

      case EvictStep(cache_idx) =>
        Evict(shard, shard', cache_idx)

      case ObserveCleanForSyncStep(cache_idx, rid) =>
        ObserveCleanForSync(shard, shard', cache_idx, rid)

      case ApplyReadStep(cache_idx, rid) =>
        ApplyRead(shard, shard', cache_idx, rid)

      case ApplyWriteStep(cache_idx, rid) =>
        ApplyWrite(shard, shard', cache_idx, rid)

      case MarkDirtyStep(cache_idx) =>
        MarkDirty(shard, shard', cache_idx)

      case HavocNewStep(cache_idx, rid, new_data) =>
        HavocNew(shard, shard', cache_idx, rid, new_data)

      case HavocEvictStep(cache_idx, rid) =>
        HavocEvict(shard, shard', cache_idx, rid)
    }
  }

  predicate Internal(shard: M, shard': M)
  {
    exists step :: InternalStep(shard, shard', step)
  }

  predicate Inv(s: M) {
    true
  }

  lemma InitImpliesInv(s: M)
  //requires Init(s)
  ensures Inv(s)
  {
  }

  lemma InternalPreservesInv(shard: M, shard': M, rest: M)
  //requires Inv(dot(shard, rest))
  //requires Internal(shard, shard')
  ensures Inv(dot(shard', rest))
  {
  }

  lemma NewTicketPreservesInv(whole: M, whole': M, rid: RequestId, input: IOIfc.Input)
  //requires Inv(whole)
  //requires NewTicket(whole, whole', rid, input)
  ensures Inv(whole')
  {
  }

  lemma ConsumeStubPreservesInv(whole: M, whole': M, rid: RequestId, output: IOIfc.Output)
  //requires Inv(whole)
  //requires ConsumeStub(whole, whole', rid, output)
  ensures Inv(whole')
  {
  }

  lemma ProcessReadPreservesInv(disk_addr: nat, data: DiskIfc.Block, rest: M)
  //requires Inv(dot(DiskReadReq(disk_addr, |data|), rest))
  ensures Inv(dot(DiskReadResp(disk_addr, data), rest))
  {
  }

  lemma ProcessWritePreservesInv(disk_addr: nat, data: DiskIfc.Block, rest: M)
  //requires Inv(dot(DiskWriteReq(disk_addr, data), rest))
  ensures Inv(dot(DiskWriteResp(disk_addr), rest))
  {
  }

  lemma dot_unit(x: M)
  ensures dot(x, unit()) == x
  {
  }

  lemma commutative(x: M, y: M)
  ensures dot(x, y) == dot(y, x)
  {
    if dot(x,y) == Fail {
      assert dot(x, y) == dot(y, x);
    } else {
      assert dot(x, y) == dot(y, x);
    }
  }

  lemma associative(x: M, y: M, z: M)
  ensures dot(x, dot(y, z)) == dot(dot(x, y), z)
  {
    if dot(x, dot(y, z)) == Fail {
      assert dot(x, dot(y, z)) == dot(dot(x, y), z);
    } else {
      assert dot(x, dot(y, z)) == dot(dot(x, y), z);
    }
  }

  lemma exists_inv_state()
  returns (s: M)
  ensures Inv(s)
  {
  }
}
