include "../framework/AIO.s.dfy"
include "rwlock/RwLock.i.dfy"

module CacheAIOParams refines AIOParams {
  import T = RwLockToken
  import opened CacheHandle
  import opened Cells
  import opened GlinearSeq

  glinear datatype IOSlotAccess = IOSlotAccess(
    glinear iocb: Iocb,
    glinear iovec: PointsToArray<Iovec>)

  glinear datatype ReadG = ReadG(
    ghost key: Key,
    glinear cache_reading: CacheResources.CacheReading,
    glinear idx: CellContents<int64>,
    glinear ro: T.Token,
    ghost slot_idx: nat,
    glinear iovec: PointsToArray<Iovec>
  )

  glinear datatype WriteG = WriteG(
    ghost key: Key,
    glinear wbo: T.WritebackObtainedToken,
    ghost slot_idx: nat,
    glinear iovec: PointsToArray<Iovec>
  )

  glinear datatype WritevG = WritevG(
    ghost keys: seq<Key>,
    glinear wbos: glseq<T.WritebackObtainedToken>,
    ghost slot_idx: nat
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

  predicate is_read_perm_v(
      iocb_ptr: Ptr,
      iocb: Iocb,
      iovec: PointsToArray<Iovec>,
      datas: seq<seq<byte>>,
      g: WritevG)
  {
    && g.wbos.len() == |datas| == |iovec.s| == |g.keys|
    && forall i | 0 <= i < g.wbos.len() ::
      && g.wbos.has(i)
      && g.wbos.get(i).is_handle(g.keys[i])
      && g.wbos.get(i).b.CacheEntryHandle?
      && g.wbos.get(i).b.data.s == datas[i]
      && g.wbos.get(i).b.data.ptr == iovec.s[i].iov_base()
  }

  glinear method get_read_perm_v(
      ghost iocb_ptr: Ptr,
      gshared iocb: Iocb,
      gshared iovec: PointsToArray<Iovec>,
      ghost datas: seq<seq<byte>>,
      gshared g: WritevG,
      ghost i: nat)
  returns (gshared ad: PointsToArray<byte>)
  //requires iocb.IocbWritev?
  //requires is_read_perm_v(iocb_ptr, iocb, iovec, datas, g)
  //requires 0 <= i < |datas| == |iovec.s|
  ensures ad == PointsToArray(iovec.s[i].iov_base(), datas[i])
  {
    ad := T.borrow_wb(g.wbos.borrow(i).token).data;
  }
}
