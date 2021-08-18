include "../../framework/DiskSSM.s.dfy"
include "CacheSpec.s.dfy"
include "../../../lib/Base/Option.s.dfy"

module CacheSSM refines DiskSSM(CacheIfc) {
  import opened Options
  import CacheIfc

  datatype Status = //Empty | Reading |
        Clean | Dirty | Writeback

  datatype Entry =
    | Empty
    | Reading(disk_idx: nat)
    | Entry(disk_idx: nat, data: DiskIfc.Block)

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
    disk_idx_to_cache_idx: map<nat, Option<nat>>,
    entries: map<nat, Entry>,
    statuses: map<nat, Status>,
    write_reqs: map<nat, DiskIfc.Block>,
    write_resps: set<nat>,
    read_reqs: set<nat>,
    read_resps: map<nat, DiskIfc.Block>,
    tickets: map<RequestId, IOIfc.Input>,
    stubs: map<RequestId, IOIfc.Output>,
    sync_reqs: map<RequestId, set<nat>>
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
        union_map(x.sync_reqs, y.sync_reqs)
      )
    else
      Fail
  }

  function DiskIdxToCacheIdx(disk_idx: nat, cache_idx: Option<nat>) : M {
    M(map[disk_idx := cache_idx],
      map[], map[], map[], {}, {}, map[], map[], map[], map[])
  }

  function CacheEntry(cache_idx: nat, disk_idx: nat, data: DiskIfc.Block) : M {
    M(map[],
      map[cache_idx := Entry(disk_idx, data)],
      map[], map[], {}, {}, map[], map[], map[], map[])
  }

  function CacheReading(cache_idx: nat, disk_idx: nat) : M {
    M(map[],
      map[cache_idx := Reading(disk_idx)],
      map[], map[], {}, {}, map[], map[], map[], map[])
  }

  function CacheEmpty(cache_idx: nat) : M {
    M(map[],
      map[cache_idx := Empty],
      map[], map[], {}, {}, map[], map[], map[], map[])
  }

  function CacheStatus(cache_idx: nat, status: Status) : M {
    M(map[], map[],
      map[cache_idx := status],
      map[], {}, {}, map[], map[], map[], map[])
  }

  function DiskWriteReq(disk_addr: nat, data: DiskIfc.Block) : M {
    M(map[], map[], map[],
      map[disk_addr := data],
      {}, {}, map[], map[], map[], map[])
  }

  function DiskWriteResp(disk_addr: nat) : M {
    M(map[], map[], map[], map[],
      {disk_addr},
      {}, map[], map[], map[], map[])
  }

  function DiskReadReq(disk_addr: nat) : M {
    M(map[], map[], map[], map[], {},
      {disk_addr},
      map[], map[], map[], map[])
  }

  function DiskReadResp(disk_addr: nat, data: DiskIfc.Block) : M {
    M(map[], map[], map[], map[], {}, {},
      map[disk_addr := data],
      map[], map[], map[])
  }

  function NormalTicket(rid: RequestId, input: IOIfc.Input) : M {
    M(map[], map[], map[], map[], {}, {}, map[],
      map[rid := input],
      map[], map[])
  }

  function NormalStub(rid: RequestId, output: IOIfc.Output) : M {
    M(map[], map[], map[], map[], {}, {}, map[], map[],
      map[rid := output],
      map[])
  }

  function SyncReq(rid: RequestId, disk_indices: set<nat>) : M {
    M(map[], map[], map[], map[], {}, {}, map[], map[], map[],
      map[rid := disk_indices])
  }

  function unit() : M {
    M(map[], map[], map[], map[], {}, {}, map[], map[], map[], map[])
  }

  function Ticket(rid: RequestId, input: IOIfc.Input) : M {
    if input.SyncInput? then
      SyncReq(rid, input.keys)
    else
      NormalTicket(rid, input)
  }

  function Stub(rid: RequestId, output: IOIfc.Output) : M {
    if output.SyncOutput? then
      SyncReq(rid, {})
    else
      NormalStub(rid, output)
  }

  // By returning a set of request ids "in use", we enforce that
  // there are only a finite number of them (i.e., it is always possible to find
  // a free one).
  function request_ids_in_use(m: M) : set<RequestId> {
    if m.M? then
      m.tickets.Keys + m.stubs.Keys + m.sync_reqs.Keys
    else
      {}
  }

  predicate Init(s: M)

  function dot3(a: M, b: M, c: M) : M {
    dot(dot(a, b), c)
  }

  function dot4(a: M, b: M, c: M, d: M) : M {
    dot(dot(dot(a, b), c), d)
  }

  predicate StartRead(shard: M, shard': M,
      cache_idx: nat, disk_idx: nat) {
    && shard == dot(
        CacheEmpty(cache_idx),
        DiskIdxToCacheIdx(disk_idx, None)
       )
    && shard' == dot3(
        CacheReading(cache_idx, disk_idx),
        DiskIdxToCacheIdx(disk_idx, Some(cache_idx)),
        DiskReadReq(disk_idx)
       )
  }

  predicate FinishRead(shard: M, shard': M,
      cache_idx: nat, disk_idx: nat, data: DiskIfc.Block) {
    && shard == dot(
        CacheReading(cache_idx, disk_idx),
        DiskReadResp(disk_idx, data)
       )
    && shard' == dot(
        CacheStatus(cache_idx, Clean),
        CacheEntry(cache_idx, disk_idx, data)
       )
  }

  predicate StartWriteback(shard: M, shard': M,
      cache_idx: nat, disk_idx: nat, data: DiskIfc.Block) {
    && shard == dot(
        CacheStatus(cache_idx, Dirty),
        CacheEntry(cache_idx, disk_idx, data)
       )
    && shard' == dot3(
        CacheStatus(cache_idx, Writeback),
        CacheEntry(cache_idx, disk_idx, data), // unchanged
        DiskWriteReq(disk_idx, data)
       )
  }

  predicate FinishWriteback(shard: M, shard': M,
      cache_idx: nat, disk_idx: nat, data: DiskIfc.Block) {
    && shard == dot3(
        CacheEntry(cache_idx, disk_idx, data),
        CacheStatus(cache_idx, Writeback),
        DiskWriteResp(disk_idx)
       )
    && shard' == dot(
        CacheEntry(cache_idx, disk_idx, data), // unchanged
        CacheStatus(cache_idx, Clean)
      )
  }

  predicate Evict(shard: M, shard': M,
      cache_idx: nat, disk_idx: nat, data: DiskIfc.Block, cache_idx2: Option<nat>) {
    && shard == dot3(
        CacheStatus(cache_idx, Clean),
        CacheEntry(cache_idx, disk_idx, data),
        DiskIdxToCacheIdx(disk_idx, cache_idx2)
      )
    && shard == dot(
        CacheEmpty(cache_idx),
        DiskIdxToCacheIdx(disk_idx, None)
      )
  }

  predicate ObserveCleanForSync(shard: M, shard': M,
    cache_idx: nat, disk_idx: nat, data: DiskIfc.Block, rid: RequestId, s: set<nat>)
  {
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
  }

  predicate ApplyRead(shard: M, shard': M,
      cache_idx: nat, disk_idx: nat, data: DiskIfc.Block, rid: RequestId)
  {
    && shard == dot(
      CacheEntry(cache_idx, disk_idx, data),
      NormalTicket(rid, CacheIfc.ReadInput(disk_idx))
    )
    && shard' == dot(
      CacheEntry(cache_idx, disk_idx, data),
      NormalStub(rid, CacheIfc.ReadOutput(data))
    )
  }

  predicate ApplyWrite(shard: M, shard': M,
      cache_idx: nat, disk_idx: nat, data: DiskIfc.Block, new_data: DiskIfc.Block,
      rid: RequestId)
  {
    && shard == dot(
      CacheEntry(cache_idx, disk_idx, data),
      NormalTicket(rid, CacheIfc.WriteInput(disk_idx, new_data))
    )
    && shard' == dot(
      CacheEntry(cache_idx, disk_idx, new_data),
      NormalStub(rid, CacheIfc.WriteOutput)
    )
  }

  predicate Internal(shard: M, shard': M)

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
