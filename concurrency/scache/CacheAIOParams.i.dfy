include "../framework/AIO.s.dfy"
include "rwlock/RwLock.i.dfy"

module CacheAIOParams refines AIOParams {
  import T = RwLockToken
  import opened CacheHandle
  import opened Cells

  datatype IOSlotInfo =
    | IOSlotWrite(cache_idx: uint64)
    | IOSlotRead(cache_idx: uint64)

  glinear datatype IOSlotAccess = IOSlotAccess(
    glinear iocb: Iocb,
    glinear io_slot_info: CellContents<IOSlotInfo>)

  glinear datatype ReadG = ReadG(
    ghost key: Key,
    glinear cache_reading: CacheResources.CacheReading,
    glinear idx: CellContents<int64>,
    glinear ro: T.Token,
    ghost slot_idx: nat,
    glinear io_slot_info: CellContents<IOSlotInfo>
  )

  glinear datatype WriteG = WriteG(
    ghost key: Key,
    glinear wbo: T.WritebackObtainedToken,
    ghost slot_idx: nat,
    glinear io_slot_info: CellContents<IOSlotInfo>
  )

  predicate is_read_perm(
      iocb_ptr: Ptr,
      iocb: Iocb,
      data: seq<byte>,
      g: WriteG)
  {
    && g.wbo.is_handle(g.key)
    && g.wbo.b.CacheEntryHandle?
    && g.wbo.b.data.s == data
    && iocb.IocbWrite?
    && g.wbo.b.data.ptr == iocb.buf
  }

  glinear method get_read_perm(
      ghost iocb_ptr: Ptr,
      gshared iocb: Iocb,
      ghost data: seq<byte>,
      gshared g: WriteG)
  returns (gshared ad: PointsToArray<byte>)
  //requires iocb.IocbWrite?
  //requires async_write_inv(iocb_ptr, iocb, data, g)
  ensures ad == PointsToArray(iocb.buf, data)
  {
    ad := T.borrow_wb(g.wbo.token).data;
  }

  /*predicate async_read_inv(
      iocb_ptr: Ptr,
      iocb: Iocb,
      wp: PointsToArray<byte>,
      g: ReadG)
  {
    && g.reading.CacheReadingHandle?
    && g.reading.is_handle(g.key)
  }*/
}
