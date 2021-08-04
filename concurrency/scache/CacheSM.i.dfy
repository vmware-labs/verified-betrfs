include "../framework/DiskSSM.s.dfy"
include "CacheSpec.s.dfy"

module CacheSSM refines DiskSSM(CacheIfc) {
  datatype Status = Empty | Reading | Clean | Dirty | Writeback

  datatype CacheEntry = CacheEntry(
    disk_idx: int, // meaningless if Status == Empty
    cache_idx: int,
    data: seq<byte>
  )

  datatype M = M(
    disk_idx_to_cache_idx: map<nat, nat>,
    entries: map<nat, CacheEntry>,
    statuses: map<nat, Status>
    disk_write_reqs: map<nat, seq<byte>>,
    disk_write_resps: set<nat>,
    disk_read_reqs: set<nat>,
    disk_read_resp: map<nat, seq<byte>>,
  ) | Fail

  function dot(x: M, y: M) : M {
    if x.M? && y.M? &&
        && disjoint_maps(x.disk_idx_to_cache_idx, y.disk_idx_to_cache_idx)
        && disjoint_maps(x.entries, y.entries)
        && disjoint_maps(x.statuses, y.statuses)
    then
      M(
        union_map(x.disk_idx_to_cache_idx, y.disk_idx_to_cache_idx),
        union_map(x.entries, y.entries),
        union_map(x.statuses, y.statuses)
      )
  }

  function unit() : M {
    M(map[], map[], map[])
  }

  function Ticket(rid: RequestId, input: IOIfc.Input) : M
  function Stub(rid: RequestId, output: IOIfc.Output) : M

  // By returning a set of request ids "in use", we enforce that
  // there are only a finite number of them (i.e., it is always possible to find
  // a free one).
  function request_ids_in_use(m: M) : set<RequestId>

  function DiskWriteReq(disk_addr: int, data: seq<byte>) : M
  function DiskWriteResp(disk_addr: int, len: int) : M

  function DiskReadReq(disk_addr: int, len: int) : M
  function DiskReadResp(disk_addr: int, data: seq<byte>) : M

  predicate Init(s: M)
  predicate Internal(shard: M, shard': M)

  predicate NewTicket(whole: M, whole': M, rid: RequestId, input: IOIfc.Input) {
    && rid !in request_ids_in_use(whole)
    && whole' == dot(whole, Ticket(rid, input))
  }

  predicate ConsumeStub(whole: M, whole': M, rid: RequestId, output: IOIfc.Output) {
    && whole == dot(whole', Stub(rid, output))
  }

  predicate Inv(s: M)

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

  lemma ProcessReadPreservesInv(disk_addr: int, data: seq<byte>, rest: M)
  requires Inv(dot(DiskReadReq(disk_addr, |data|), rest))
  ensures Inv(dot(DiskReadResp(disk_addr, data), rest))

  lemma ProcessWritePreservesInv(disk_addr: int, data: seq<byte>, rest: M)
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

}
