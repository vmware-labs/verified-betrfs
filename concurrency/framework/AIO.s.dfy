include "../../lib/Lang/NativeTypes.s.dfy"
include "Ptrs.s.dfy"
include "DiskSSM.s.dfy"
include "GlinearSeq.s.dfy"

module PageSizeConstant {
  import opened NativeTypes
  const PageSize: uint64 := 4096
}

module {:extern "IocbStruct"} IocbStruct {
  import opened Ptrs
  import opened NativeTypes
  import opened GlinearSeq
  import opened PageSizeConstant

  /*
   * iocb type
   *
   * implemented externally by iocb struct
   */

  datatype Iocb =
    | IocbUninitialized(ptr: Ptr)
    | IocbRead(ptr: Ptr, ghost offset: nat, ghost nbytes: nat, buf: Ptr)
    | IocbWrite(ptr: Ptr, ghost offset: nat, ghost nbytes: nat, buf: Ptr)
    | IocbWritev(ptr: Ptr, ghost offset: nat, ghost iovec: Ptr, iovec_len: nat)

  function method {:extern} SizeOfIocb() : uint64
  ensures SizeOfIocb() != 0

  method {:extern} new_iocb()
  returns (ptr: Ptr, glinear iocb: Iocb)
  ensures iocb.IocbUninitialized?
  ensures iocb.ptr == ptr

  method {:extern} new_iocb_array(n: uint64)
  returns (ptr: Ptr, glinear iocb: glseq<Iocb>)
  ensures iocb.len() == n as int
  ensures forall i {:trigger iocb.has(i)} {:trigger iocb.get(i)} | 0 <= i < n as int
      :: iocb.has(i)
      && iocb.get(i).IocbUninitialized?
      && 0 <= i * SizeOfIocb() as int < 0x1_0000_0000_0000_0000
      && 0 <= ptr.as_nat() + i * SizeOfIocb() as int < 0x1_0000_0000_0000_0000
      && iocb.get(i).ptr == ptr_add(ptr, i as uint64 * SizeOfIocb())

  method {:extern} iocb_prepare_read(ptr: Ptr, glinear inout iocb: Iocb,
      offset: int64, nbytes: uint64, buf: Ptr)
  requires offset >= 0
  requires PageSize as int * offset as int < 0x1000_0000_0000_0000
  requires old_iocb.ptr == ptr
  requires buf.aligned(PageSize as int) // O_DIRECT requires data to be aligned
  ensures iocb == IocbRead(ptr, offset as nat, nbytes as nat, buf)

  method {:extern} iocb_prepare_write(ptr: Ptr, glinear inout iocb: Iocb,
      offset: int64, nbytes: uint64, buf: Ptr)
  requires offset >= 0
  requires old_iocb.ptr == ptr
  requires PageSize as int * offset as int < 0x1000_0000_0000_0000
  requires buf.aligned(PageSize as int)
  ensures iocb == IocbWrite(ptr, offset as nat, nbytes as nat, buf)

  method {:extern} iocb_prepare_writev(ptr: Ptr, glinear inout iocb: Iocb,
      offset: int64, iovec: Ptr, iovec_len: uint64)
  requires offset >= 0
  ensures iocb == IocbWritev(ptr, offset as nat, iovec, iovec_len as nat)

  method {:extern} iocb_is_read(ptr: Ptr, gshared iocb: Iocb)
  returns (b: bool)
  requires iocb.ptr == ptr
  requires !iocb.IocbUninitialized?
  ensures b == iocb.IocbRead?

  method {:extern} iocb_is_write(ptr: Ptr, gshared iocb: Iocb)
  returns (b: bool)
  requires iocb.ptr == ptr
  requires !iocb.IocbUninitialized?
  ensures b == iocb.IocbWrite?

  method {:extern} iocb_is_writev(ptr: Ptr, gshared iocb: Iocb)
  returns (b: bool)
  requires iocb.ptr == ptr
  requires !iocb.IocbUninitialized?
  ensures b == iocb.IocbWritev?

  method {:extern} iocb_buf(ptr: Ptr, gshared iocb: Iocb)
  returns (buf: Ptr)
  requires iocb.ptr == ptr
  requires iocb.IocbRead? || iocb.IocbWrite?
  ensures buf == iocb.buf

  method {:extern} iocb_iovec(ptr: Ptr, gshared iocb: Iocb)
  returns (iovec: Ptr)
  requires iocb.ptr == ptr
  requires iocb.IocbWritev?
  ensures iovec == iocb.iovec

  method {:extern} iocb_iovec_len(ptr: Ptr, gshared iocb: Iocb)
  returns (iovec_len: uint64)
  requires iocb.ptr == ptr
  requires iocb.IocbWritev?
  ensures iovec_len as int == iocb.iovec_len


  type {:extern "struct"} Iovec(!new) {
    function method {:extern} iov_base() : Ptr
    function method {:extern} iov_len() : uint64
  }

  method {:extern} new_iovec(base: Ptr, len: uint64)
  returns (iovec: Iovec)
  ensures iovec.iov_base() == base
  ensures iovec.iov_len() == len
}

abstract module AIOParams {
  import opened Ptrs
  import opened IocbStruct
  import opened NativeTypes
  type ReadG(!new)
  type WriteG(!new)
  type WritevG(!new)

  predicate is_read_perm(
      iocb_ptr: Ptr,
      iocb: Iocb,
      data: seq<byte>,
      g: WriteG)

  predicate is_read_perm_v(
      iocb_ptr: Ptr,
      iocb: Iocb,
      iovec: PointsToArray<Iovec>,
      datas: seq<seq<byte>>,
      g: WritevG)

  glinear method get_read_perm(
      ghost iocb_ptr: Ptr,
      gshared iocb: Iocb,
      ghost data: seq<byte>,
      gshared g: WriteG)
  returns (gshared ad: PointsToArray<byte>)
  requires iocb.IocbWrite?
  requires is_read_perm(iocb_ptr, iocb, data, g)
  ensures ad == PointsToArray(iocb.buf, data)

  glinear method get_read_perm_v(
      ghost iocb_ptr: Ptr,
      gshared iocb: Iocb,
      gshared iovec: PointsToArray<Iovec>,
      ghost datas: seq<seq<byte>>,
      gshared g: WritevG,
      ghost i: nat)
  returns (gshared ad: PointsToArray<byte>)
  requires iocb.IocbWritev?
  requires is_read_perm_v(iocb_ptr, iocb, iovec, datas, g)
  requires 0 <= i < |datas| <= |iovec.s|
  ensures ad == PointsToArray(iovec.s[i].iov_base(), datas[i])
}

abstract module AIO(aioparams: AIOParams, ioifc: InputOutputIfc, ssm: DiskSSM(ioifc)) {
  import opened NativeTypes
  import opened IocbStruct
  import opened Ptrs
  import opened PageSizeConstant
  import opened GlinearSeq
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

    predicate async_writev_inv(
      iocb_ptr: Ptr,
      iocb: Iocb,
      iovec: PointsToArray<Iovec>,
      datas: seq<seq<byte>>,
      g: aioparams.WritevG)
  }

  method {:extern} init_ctx(
      ghost async_read_inv: (Ptr, Iocb, PointsToArray<byte>, aioparams.ReadG) -> bool,
      ghost async_write_inv: (Ptr, Iocb, seq<byte>, aioparams.WriteG) -> bool,
      ghost async_writev_inv: (Ptr, Iocb, PointsToArray<Iovec>, seq<seq<byte>>, aioparams.WritevG) -> bool
    )
  returns (linear ioctx: IOCtx)
  ensures ioctx.async_read_inv == async_read_inv
  ensures ioctx.async_write_inv == async_write_inv
  ensures ioctx.async_writev_inv == async_writev_inv

  method {:extern} async_write(
      shared ctx: IOCtx,
      iocb_ptr: Ptr,
      glinear iocb: Iocb,
      ghost data: seq<byte>,
      glinear g: aioparams.WriteG,
      glinear ticket: T.Token)
  requires iocb.IocbWrite?
  requires iocb.ptr == iocb_ptr
  requires iocb.nbytes == PageSize as int
  requires |data| == iocb.nbytes
  requires iocb.nbytes > 0
  requires aioparams.is_read_perm(iocb_ptr, iocb, data, g)
  requires ctx.async_write_inv(iocb_ptr, iocb, data, g)
  requires ticket == T.Token(ssm.DiskWriteReq(iocb.offset, data))

  predicate writev_valid_i(iovec: Iovec, data: seq<byte>, ticket: T.Token, offset: nat, i: nat)
  {
    && iovec.iov_len() as int == PageSize as int
    && iovec.iov_base().aligned(PageSize as int)
    && |data| == iovec.iov_len() as int
    && ticket == T.Token(ssm.DiskWriteReq(offset + i, data))
  }

  method {:extern} async_writev(
      shared ctx: IOCtx,
      iocb_ptr: Ptr,
      glinear iocb: Iocb,
      glinear iovec: PointsToArray<Iovec>,
      ghost datas: seq<seq<byte>>,
      glinear g: aioparams.WritevG,
      glinear tickets: glseq<T.Token>)
  requires iocb.IocbWritev?
  requires iocb.ptr == iocb_ptr
  requires iocb.iovec_len > 0
  requires iovec.ptr == iocb.iovec
  requires |iovec.s| >= iocb.iovec_len == |datas| == tickets.len()
  requires forall i | 0 <= i < iocb.iovec_len ::
      tickets.has(i)
      && writev_valid_i(iovec.s[i], datas[i], tickets.get(i), iocb.offset, i)
  requires aioparams.is_read_perm_v(iocb_ptr, iocb, iovec, datas, g)
  requires ctx.async_writev_inv(iocb_ptr, iocb, iovec, datas, g)

  method {:extern} async_read(
      shared ctx: IOCtx,
      iocb_ptr: Ptr,
      glinear iocb: Iocb,
      glinear wp: PointsToArray<byte>,
      glinear g: aioparams.ReadG,
      glinear ticket: T.Token)
  requires iocb.IocbRead?
  requires iocb.ptr == iocb_ptr
  requires iocb.nbytes == PageSize as int
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
    | FRWritev(
      glinear iocb: Iocb,
      glinear iovec: PointsToArray<Iovec>,
      ghost datas: seq<seq<byte>>,
      glinear wvg: aioparams.WritevG,
      glinear stubs: glseq<T.Token>
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
  ensures iocb_ptr == nullptr() ==> fr.FRNone?
  ensures iocb_ptr != nullptr() ==> (fr.FRWrite? || fr.FRRead? || fr.FRWritev?)
  ensures fr.FRWrite? ==>
    && fr.iocb.IocbWrite?
    && ctx.async_write_inv(iocb_ptr, fr.iocb, fr.data, fr.wg)
    && fr.stub == T.Token(ssm.DiskWriteResp(fr.iocb.offset))
  ensures fr.FRWritev? ==>
    && fr.iocb.IocbWritev?
    && ctx.async_writev_inv(iocb_ptr, fr.iocb, fr.iovec, fr.datas, fr.wvg)
    && fr.stubs.len() == fr.iocb.iovec_len as int
    && forall i | 0 <= i < fr.iocb.iovec_len ::
        fr.stubs.has(i) && fr.stubs.get(i) == T.Token(ssm.DiskWriteResp(fr.iocb.offset + i))
  ensures fr.FRRead? ==>
    && fr.iocb.IocbRead?
    && ctx.async_read_inv(iocb_ptr, fr.iocb, fr.wp, fr.rg)
    && |fr.wp.s| == fr.iocb.nbytes
    && fr.iocb.nbytes == 4096
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
  requires nbytes as int == PageSize as int
  requires PageSize as int * offset as int < 0x1_0000_0000_0000_0000
  requires ticket == T.Token(ssm.DiskReadReq(offset as int))
  requires buf.aligned(PageSize as int)
  ensures wp.ptr == buf
  ensures |wp.s| == nbytes as int
  ensures stub == T.Token(ssm.DiskReadResp(offset as int, wp.s))

  method {:extern} sync_write(
      buf: Ptr,
      nbytes: uint64,
      offset: uint64,
      gshared rp: PointsToArray<byte>,
      glinear ticket: T.Token)
  returns (glinear stub: T.Token)
  requires rp.ptr == buf
  requires |rp.s| == nbytes as int
  requires nbytes as int == PageSize as int
  requires PageSize as int * offset as int < 0x1_0000_0000_0000_0000
  requires ticket == T.Token(ssm.DiskWriteReq(offset as int, rp.s))
  requires buf.aligned(PageSize as int)
  ensures rp.ptr == buf
  ensures |rp.s| == nbytes as int
  ensures stub == T.Token(ssm.DiskWriteResp(offset as int))
}
