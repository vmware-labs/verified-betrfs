include "../../lib/Lang/NativeTypes.s.dfy"
include "Ptrs.s.dfy"
include "DiskSSM.s.dfy"

module IocbStruct {
  import opened Ptrs
  import opened NativeTypes

  const PageSize := 4096

  /*
   * iocb type
   *
   * implemented externally by iocb struct
   */

  datatype Iocb =
    | IocbUninitialized(ptr: Ptr)
    | IocbRead(ptr: Ptr, offset: nat, nbytes: nat, buf: Ptr)
    | IocbWrite(ptr: Ptr, offset: nat, nbytes: nat, buf: Ptr)

  function method SizeOfIocb() : uint64
  ensures SizeOfIocb() != 0

  method {:extern} new_iocb()
  returns (ptr: Ptr, glinear iocb: Iocb)
  ensures iocb.IocbUninitialized?

  method {:extern} iocb_prepare_read(ptr: Ptr, glinear inout iocb: Iocb,
      offset: int64, nbytes: uint64, buf: Ptr)
  requires offset >= 0
  requires PageSize * offset as int < 0x1000_0000_0000_0000
  requires old_iocb.ptr == ptr
  requires buf.aligned(PageSize)
  ensures iocb == IocbRead(ptr, offset as nat, nbytes as nat, buf)

  method {:extern} iocb_prepare_write(ptr: Ptr, glinear inout iocb: Iocb,
      offset: int64, nbytes: uint64, buf: Ptr)
  requires offset >= 0
  requires old_iocb.ptr == ptr
  requires PageSize * offset as int < 0x1000_0000_0000_0000
  requires buf.aligned(PageSize)
  ensures iocb == IocbWrite(ptr, offset as nat, nbytes as nat, buf)
}

abstract module AIOParams {
  import opened Ptrs
  import opened IocbStruct
  import opened NativeTypes
  type ReadG(!new)
  type WriteG(!new)

  predicate is_read_perm(
      iocb_ptr: Ptr,
      iocb: Iocb,
      data: seq<byte>,
      g: WriteG)

  glinear method get_read_perm(
      ghost iocb_ptr: Ptr,
      gshared iocb: Iocb,
      ghost data: seq<byte>,
      gshared g: WriteG)
  returns (gshared ad: PointsToArray<byte>)
  requires iocb.IocbWrite?
  requires is_read_perm(iocb_ptr, iocb, data, g)
  ensures ad == PointsToArray(iocb.buf, data)
}

abstract module AIO(aioparams: AIOParams, ioifc: InputOutputIfc, ssm: DiskSSM(ioifc)) {
  import opened NativeTypes
  import opened IocbStruct
  import opened Ptrs
  import T = DiskSSMTokens(ioifc, ssm)

  /*
   * DiskInterface
   */

  type {:extern} IOCtx
  {
    predicate async_read_inv(
      iocb_ptr: Ptr,
      iocb: Iocb,
      wp: PointsToArray<byte>,
      g: aioparams.ReadG)

    predicate async_write_inv(
      iocb_ptr: Ptr,
      iocb: Iocb,
      data: seq<byte>,
      g: aioparams.WriteG)
  }

  method {:extern} async_write(
      shared ctx: IOCtx,
      iocb_ptr: Ptr,
      glinear iocb: Iocb,
      ghost data: seq<byte>,
      glinear g: aioparams.WriteG,
      glinear ticket: T.Token)
  requires iocb.IocbWrite?
  requires iocb.ptr == iocb_ptr
  requires iocb.nbytes == PageSize
  requires |data| == iocb.nbytes
  requires iocb.nbytes > 0
  requires aioparams.is_read_perm(iocb_ptr, iocb, data, g)
  requires ctx.async_write_inv(iocb_ptr, iocb, data, g)
  requires ticket == T.Token(ssm.DiskWriteReq(iocb.offset, data))

  method {:extern} async_read(
      shared ctx: IOCtx,
      iocb_ptr: Ptr,
      glinear iocb: Iocb,
      glinear wp: PointsToArray<byte>,
      glinear g: aioparams.ReadG,
      glinear ticket: T.Token)
  requires iocb.IocbRead?
  requires iocb.ptr == iocb_ptr
  requires iocb.nbytes == PageSize
  requires wp.ptr == iocb.buf
  requires |wp.s| == iocb.nbytes
  requires ctx.async_read_inv(iocb_ptr, iocb, wp, g)
  requires ticket == T.Token(ssm.DiskReadReq(iocb.offset))

  glinear datatype FinishedReq =
    | FRNone
    | FRWrite(
      glinear iocb: Iocb,
      ghost data: seq<byte>,
      glinear wg: aioparams.WriteG,
      glinear stub: T.Token
    )
    | FRRead(
      glinear iocb: Iocb,
      glinear wp: PointsToArray<byte>,
      glinear rg: aioparams.ReadG,
      glinear stub: T.Token
    )

  method {:extern} get_event(shared ctx: IOCtx)
  returns (
    iocb_ptr: Ptr,
    glinear fr: FinishedReq
  )
  ensures iocb_ptr == nullptr ==> fr.FRNone?
  ensures iocb_ptr != nullptr ==> (fr.FRWrite? || fr.FRRead?)
  ensures fr.FRWrite? ==>
    && fr.iocb.IocbWrite?
    && ctx.async_write_inv(iocb_ptr, fr.iocb, fr.data, fr.wg)
    && fr.stub == T.Token(ssm.DiskWriteResp(fr.iocb.offset))
  ensures fr.FRRead? ==>
    && fr.iocb.IocbRead?
    && ctx.async_read_inv(iocb_ptr, fr.iocb, fr.wp, fr.rg)
    && |fr.wp.s| == fr.iocb.nbytes
    && fr.stub == T.Token(ssm.DiskReadResp(fr.iocb.offset, fr.wp.s))

  method {:extern} sync_read(
      buf: Ptr,
      nbytes: uint64,
      offset: uint64,
      glinear inout wp: PointsToArray<byte>,
      glinear ticket: T.Token)
  returns (glinear stub: T.Token)
  requires old_wp.ptr == buf
  requires |old_wp.s| == nbytes as int
  requires nbytes as int == PageSize
  requires PageSize * offset as int < 0x1_0000_0000_0000_0000
  requires ticket == T.Token(ssm.DiskReadReq(offset as int))
  requires buf.aligned(PageSize)
  ensures wp.ptr == buf
  ensures |wp.s| == nbytes as int
  ensures stub == T.Token(ssm.DiskReadResp(offset as int, wp.s))
}
