include "CacheOps.i.dfy"

// Really simple application exercising the cache.

module Application(aio: AIO(CacheAIOParams, CacheIfc, CacheSSM)) {
  import opened CT = CacheTypes(aio)
  import opened NativeTypes
  import opened RequestIds
  import CacheOps = CacheOps(aio)
  import CacheSSM
  import CacheIfc
  import DiskIfc
  import opened Constants
  import T = DiskSSMTokens(CacheIfc, CacheSSM)
  import opened ClientCounter
  import RwLockToken
  import opened Ptrs
  import CacheResources

  method copy_seq(ptr: Ptr, gshared d: PointsToArray<byte>)
  returns (s: seq<byte>)
  requires |d.s| == 4096
  requires d.ptr == ptr
  ensures s == d.s

  method read_block(
      shared cache: Cache,
      inout linear localState: LocalState,
      disk_idx: uint64,
      ghost rid: RequestId,
      glinear ticket: T.Token,
      glinear client: Client)
  returns (block: DiskIfc.Block, glinear stub: T.Token, glinear client': Client)
  requires cache.Inv()
  requires old_localState.WF()
  requires 0 <= disk_idx as int < NUM_DISK_PAGES
  requires ticket.val == CacheSSM.Ticket(rid, CacheIfc.ReadInput(disk_idx as int))
  ensures localState.WF()
  ensures stub.val == CacheSSM.Stub(rid, CacheIfc.ReadOutput(block))
  decreases *
  {
    var ph;
    glinear var handle;
    ph, handle := CacheOps.get(cache, inout localState, disk_idx, client);

    block := copy_seq(ph.ptr, RwLockToken.borrow_sot(handle.so).data);
    stub := CacheResources. app_read_block(
        rid, RwLockToken.borrow_sot(handle.so).cache_entry, ticket);

    client' := CacheOps.unget(cache, localState, ph, disk_idx, handle);
  }
}
