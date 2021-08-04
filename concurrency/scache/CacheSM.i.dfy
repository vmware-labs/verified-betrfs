include "../framework/DiskSSM.s.dfy"
include "CacheSpec.s.dfy"
include "../../lib/Base/Option.s.dfy"

module CacheSSM refines DiskSSM(CacheIfc) {
  import opened Options

  datatype Status = Empty | Reading | Clean | Dirty | Writeback

  datatype Entry = Entry(
    disk_idx: nat, // meaningless if Status == Empty
    data: seq<byte> // meaningless if Status in {Empty, Reading}
  )

  datatype M = M(
    disk_idx_to_cache_idx: map<nat, Option<nat>>,
    entries: map<nat, Entry>,
    statuses: map<nat, Status>,
    write_reqs: map<nat, seq<byte>>,
    write_resps: set<nat>,
    read_reqs: set<nat>,
    read_resps: map<nat, seq<byte>>,
    tickets: map<RequestId, IOIfc.Input>,
    stubs: map<RequestId, IOIfc.Output>
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
        union_map(x.stubs, y.stubs)
      )
    else
      Fail
  }

  function DiskIdxToCacheIdx(disk_idx: nat, cache_idx: Option<nat>) : M {
    M(map[disk_idx := cache_idx],
      map[], map[], map[], {}, {}, map[], map[], map[])
  }

  function CacheEntry(cache_idx: nat, disk_idx: nat, data: seq<byte>) : M {
    M(map[],
      map[cache_idx := Entry(disk_idx, data)],
      map[], map[], {}, {}, map[], map[], map[])
  }

  function CacheStatus(cache_idx: nat, status: Status) : M {
    M(map[], map[],
      map[cache_idx := status],
      map[], {}, {}, map[], map[], map[])
  }

  function WriteReq(disk_idx: nat, data: seq<byte>) : M {
    M(map[], map[], map[],
      map[disk_idx := data],
      {}, {}, map[], map[], map[])
  }

  function WriteResp(disk_idx: nat) : M {
    M(map[], map[], map[], map[],
      {disk_idx},
      {}, map[], map[], map[])
  }

  function ReadReq(disk_idx: nat) : M {
    M(map[], map[], map[], map[], {},
      {disk_idx},
      map[], map[], map[])
  }

  function ReadResp(disk_idx: nat, data: seq<byte>) : M {
    M(map[], map[], map[], map[], {}, {},
      map[disk_idx := data],
      map[], map[])
  }

  function unit() : M {
    M(map[], map[], map[], map[], {}, {}, map[], map[], map[])
  }

  function Ticket(rid: RequestId, input: IOIfc.Input) : M
  function Stub(rid: RequestId, output: IOIfc.Output) : M

  // By returning a set of request ids "in use", we enforce that
  // there are only a finite number of them (i.e., it is always possible to find
  // a free one).
  function request_ids_in_use(m: M) : set<RequestId> {
    if m.M? then
      m.tickets.Keys + m.stubs.Keys
    else
      {}
  }

  function DiskWriteReq(disk_addr: nat, data: seq<byte>) : M
  function DiskWriteResp(disk_addr: nat, len: nat) : M

  function DiskReadReq(disk_addr: nat, len: nat) : M
  function DiskReadResp(disk_addr: nat, data: seq<byte>) : M

  predicate Init(s: M)

  function dot3(a: M, b: M, c: M) : M {
    dot(dot(a, b), c)
  }

  function dot4(a: M, b: M, c: M, d: M) : M {
    dot(dot(dot(a, b), c), d)
  }

  predicate StartRead(shard: M, shard': M,
      cache_idx: nat, disk_idx: nat, junk_data: seq<byte>, junk_disk_idx: nat) {
    && shard == dot3(
        CacheStatus(cache_idx, Empty),
        CacheEntry(cache_idx, junk_disk_idx, junk_data),
        DiskIdxToCacheIdx(disk_idx, None)
       )
    && shard' == dot4(
        CacheStatus(cache_idx, Reading),
        CacheEntry(cache_idx, disk_idx, junk_data),
        DiskIdxToCacheIdx(disk_idx, Some(cache_idx)),
        ReadReq(disk_idx)
       )
  }

  predicate FinishRead(shard: M, shard': M,
      cache_idx: nat, disk_idx: nat, junk_data: seq<byte>, data: seq<byte>,
      status: Status) {
    && shard == dot3(
        CacheStatus(cache_idx, status),
        CacheEntry(cache_idx, disk_idx, junk_data),
        ReadResp(disk_idx, data)
       )
    && shard' == dot(
        CacheStatus(cache_idx, Clean),
        CacheEntry(cache_idx, disk_idx, data)
       )
  }

  predicate StartWriteback(shard: M, shard': M,
      cache_idx: nat, disk_idx: nat, data: seq<byte>) {
    && shard == dot(
        CacheStatus(cache_idx, Dirty),
        CacheEntry(cache_idx, disk_idx, data)
       )
    && shard' == dot3(
        CacheStatus(cache_idx, Writeback),
        CacheEntry(cache_idx, disk_idx, data),
        WriteReq(disk_idx, data)
       )
  }

  predicate FinishWriteback(shard: M, shard': M,
      cache_idx: nat, disk_idx: nat, data: seq<byte>, status: Status) {
    && shard == dot(
        CacheStatus(cache_idx, status),
        WriteResp(disk_idx)
       )
    && shard' == 
        CacheStatus(cache_idx, Clean)
  }

  predicate Evict(shard: M, shard': M,
      cache_idx: nat, disk_idx: nat, data: seq<byte>, cache_idx2: Option<nat>) {
    && shard == dot3(
        CacheStatus(cache_idx, Clean),
        CacheEntry(cache_idx, disk_idx, data),
        DiskIdxToCacheIdx(disk_idx, cache_idx2)
      )
    && shard == dot3(
        CacheStatus(cache_idx, Empty),
        CacheEntry(cache_idx, disk_idx, data),
        DiskIdxToCacheIdx(disk_idx, None)
      )
  }

  predicate Internal(shard: M, shard': M)

  predicate Inv(s: M) {
    true
  }

/*
  lemma InitImpliesInv(s: M)
  requires Init(s)
  ensures Inv(s)

  lemma InternalPreservesInv(shard: M, shard': M, rest: M)
  requires Inv(dot(shard, rest))
  requires Internal(shard, shard')
  ensures Inv(dot(shard', rest))

  lemma NewTicketPreservesInv(whole: M, whole': M, rid: RequestId, input: IOIfc.Input)
  requires Inv(whole)
  requires NewTicket(whole, whole', rid, input)
  ensures Inv(whole')

  lemma ConsumeStubPreservesInv(whole: M, whole': M, rid: RequestId, output: IOIfc.Output)
  requires Inv(whole)
  requires ConsumeStub(whole, whole', rid, output)
  ensures Inv(whole')

  lemma ProcessReadPreservesInv(disk_addr: nat, data: seq<byte>, rest: M)
  requires Inv(dot(DiskReadReq(disk_addr, |data|), rest))
  ensures Inv(dot(DiskReadResp(disk_addr, data), rest))

  lemma ProcessWritePreservesInv(disk_addr: nat, data: seq<byte>, rest: M)
  requires Inv(dot(DiskWriteReq(disk_addr, data), rest))
  ensures Inv(dot(DiskWriteResp(disk_addr, |data|), rest))

  lemma dot_unit(x: M)
  ensures dot(x, unit()) == x

  lemma commutative(x: M, y: M)
  ensures dot(x, y) == dot(y, x)

  lemma associative(x: M, y: M, z: M)
  ensures dot(x, dot(y, z)) == dot(dot(x, y), z)

  lemma exists_inv_state()
  returns (s: M)
  ensures Inv(s)

*/
}
