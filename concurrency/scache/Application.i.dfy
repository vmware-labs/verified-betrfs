include "CacheOps.i.dfy"
include "CacheInit.i.dfy"

// Really simple application exercising the cache.

module Application(aio: AIO(CacheAIOParams, CacheIfc, CacheSSM)) {
  import opened CT = CacheTypes(aio)
  import opened NativeTypes
  import opened RequestIds
  import opened CacheOps = CacheOps(aio)
  import CacheSSM
  import CacheIfc
  import DiskIfc
  import opened Constants
  import T = DiskSSMTokens(CacheIfc, CacheSSM)
  import opened ClientCounter
  import RwLockToken
  import opened Ptrs
  import CacheResources
  import opened CacheHandle

  method copy_seq_out(ptr: Ptr, gshared d: PointsToArray<byte>)
  returns (s: seq<byte>)
  requires |d.s| == 4096
  requires d.ptr == ptr
  ensures s == d.s

  method copy_seq_in(ptr: Ptr, inout glinear d: PointsToArray<byte>, data: seq<byte>)
  requires old_d.ptr == ptr
  requires |old_d.s| == 4096
  requires |data| == 4096
  ensures d == old_d.(s := data)

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
  requires 0 <= disk_idx as int < NUM_DISK_PAGES as int
  requires ticket.val == CacheSSM.Ticket(rid, CacheIfc.ReadInput(disk_idx as int))
  ensures localState.WF()
  ensures stub.val == CacheSSM.Stub(rid, CacheIfc.ReadOutput(block))
  decreases *
  {
    var ph;
    glinear var handle;
    ph, handle := CacheOps.get(cache, inout localState, disk_idx, client);

    block := copy_seq_out(ph.ptr, RwLockToken.borrow_sot(handle.so).data);
    stub := CacheResources.app_read_block(
        rid, RwLockToken.borrow_sot(handle.so).cache_entry, ticket);

    client' := CacheOps.unget(cache, localState, ph, disk_idx, handle);
  }

  method write_block(
      shared cache: Cache,
      inout linear localState: LocalState,
      disk_idx: uint64,
      data: DiskIfc.Block,
      ghost rid: RequestId,
      glinear ticket: T.Token,
      glinear client: Client)
  returns (glinear stub: T.Token, glinear client': Client)
  requires cache.Inv()
  requires old_localState.WF()
  requires 0 <= disk_idx as int < NUM_DISK_PAGES as int
  requires ticket.val == CacheSSM.Ticket(rid, CacheIfc.WriteInput(disk_idx as int, data))
  ensures localState.WF()
  ensures stub.val == CacheSSM.Stub(rid, CacheIfc.WriteOutput)
  decreases *
  {
    var ph;
    glinear var write_handle;
    ph, write_handle := CacheOps.get_claim_lock(cache, inout localState, disk_idx, client);

    write_handle := CacheOps.mark_dirty(cache, localState, ph, disk_idx, write_handle);

    glinear var WriteablePageHandle(cache_idx, handle, status, eo) := write_handle;
    glinear var CacheEntryHandle(key, cache_entry, idx, pointsto) := handle;

    copy_seq_in(ph.ptr, inout pointsto, data);
    cache_entry, stub := CacheResources.app_write_block(
        rid, data, cache_entry, ticket);

    handle := CacheEntryHandle(key, cache_entry, idx, pointsto);
    write_handle := WriteablePageHandle(cache_idx, handle, status, eo);

    glinear var claim_handle := CacheOps.unlock(cache, localState, ph, disk_idx, write_handle);
    glinear var read_handle := CacheOps.unclaim(cache, localState, ph, disk_idx, claim_handle);
    client' := CacheOps.unget(cache, localState, ph, disk_idx, read_handle);
  }
}

// TODO move this to a .s file or something
module {:extern "InstantiatedDiskInterface"}
    TheAIO refines AIO(CacheAIOParams, CacheIfc, CacheSSM) { }

import App = Application(TheAIO)
