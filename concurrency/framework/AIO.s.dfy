include "../../lib/Lang/NativeTypes.s.dfy"
include "Ptrs.s.dfy"
include "DiskSSM.s.dfy"

module IocbStruct {
  import opened Ptrs
  import opened NativeTypes

  /*
   * iocb type
   *
   * implemented externally by iocb struct
   */

  datatype Iocb =
    | IocbUninitialized(ptr: Ptr)
    | IocbRead(ptr: Ptr, offset: nat, nbytes: nat, buf: Ptr)
    | IocbWrite(ptr: Ptr, offset: nat, nbytes: nat, buf: Ptr)

  method {:extern} new_iocb()
  returns (ptr: Ptr, glinear iocb: Iocb)
  ensures iocb.IocbUninitialized?

  method {:extern} iocb_prepare_read(ptr: Ptr, glinear inout iocb: Iocb,
      offset: int64, nbytes: uint64, buf: Ptr)
  requires offset >= 0
  requires PageSize * offset as int < 0x1000_0000_0000_0000
  requires old_iocb.ptr == ptr
  ensures iocb == IocbRead(ptr, offset as nat, nbytes as nat, buf)

  method {:extern} iocb_prepare_write(ptr: Ptr, glinear inout iocb: Iocb,
      offset: int64, nbytes: uint64, buf: Ptr)
  requires offset >= 0
  requires old_iocb.ptr == ptr
  requires PageSize * offset as int < 0x1000_0000_0000_0000
  ensures iocb == IocbWrite(ptr, offset as nat, nbytes as nat, buf)
}

abstract module AIOParams {
  import opened Ptrs
  import opened IocbStruct
  import opened NativeTypes
  type ReadG(!new)
  type WriteG(!new)

  predicate async_write_inv(
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
  requires async_write_inv(iocb_ptr, iocb, data, g)
  ensures ad == PointsToArray(iocb.buf, data)

  predicate async_read_inv(
      iocb_ptr: Ptr,
      iocb: Iocb,
      wp: PointsToArray<byte>,
      g: ReadG)
}

abstract module AIO(aioparams: AIOParams, ioifc: InputOutputIfc, ssm: DiskSSM(ioifc)) {
  import opened NativeTypes
  import opened IocbStruct
  import opened Ptrs
  import T = DiskSSMTokens(ioifc, ssm)

  const PageSize := 4096

  /*
   * DiskInterface
   */

  method {:extern} async_write<G>(
      iocb_ptr: Ptr,
      glinear iocb: Iocb,
      ghost data: seq<byte>,
      glinear g: aioparams.WriteG,
      glinear ticket: T.Token)
  requires iocb.IocbWrite?
  requires iocb.ptr == iocb_ptr
  requires iocb.offset % PageSize == 0
  requires iocb.nbytes == PageSize
  requires |data| == iocb.nbytes
  requires iocb.nbytes > 0
  requires aioparams.async_write_inv(iocb_ptr, iocb, data, g)
  requires ticket == T.Token(ssm.DiskWriteReq(iocb.offset / PageSize, data))

  method {:extern} async_read(
      iocb_ptr: Ptr,
      glinear iocb: Iocb,
      glinear wp: PointsToArray<byte>,
      glinear g: aioparams.ReadG,
      glinear ticket: T.Token)
  requires iocb.IocbRead?
  requires iocb.ptr == iocb_ptr
  requires iocb.offset % PageSize == 0
  requires iocb.nbytes == PageSize
  requires aioparams.async_read_inv(iocb_ptr, iocb, wp, g)
  requires ticket == T.Token(ssm.DiskReadReq(iocb.offset / PageSize))

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

  method {:extern} get_event()
  returns (
    iocb_ptr: Ptr,
    glinear fr: FinishedReq
  )
  ensures iocb_ptr == nullptr ==> fr.FRNone?
  ensures iocb_ptr != nullptr ==> (fr.FRWrite? || fr.FRRead?)
  ensures fr.FRWrite? ==>
    && fr.iocb.IocbRead?
    && aioparams.async_write_inv(iocb_ptr, fr.iocb, fr.data, fr.wg)
  ensures fr.FRRead? ==>
    && fr.iocb.IocbRead?
    && aioparams.async_read_inv(iocb_ptr, fr.iocb, fr.wp, fr.rg)
}
