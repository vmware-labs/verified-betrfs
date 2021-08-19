include "PCM.s.dfy"
include "StateMachines.s.dfy"
include "AsyncDisk.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"

abstract module DiskSSM(IOIfc: InputOutputIfc) {
  import opened RequestIds
  import opened NativeTypes
  import DiskIfc

  type M(!new)

  function dot(x: M, y: M) : M
  function unit() : M

  function Ticket(rid: RequestId, input: IOIfc.Input) : M
  function Stub(rid: RequestId, output: IOIfc.Output) : M

  // By returning a set of request ids "in use", we enforce that
  // there are only a finite number of them (i.e., it is always possible to find
  // a free one).
  function request_ids_in_use(m: M) : set<RequestId>

  function DiskWriteReq(disk_addr: nat, data: DiskIfc.Block) : M
  function DiskWriteResp(disk_addr: nat) : M

  function DiskReadReq(disk_addr: nat) : M
  function DiskReadResp(disk_addr: nat, data: DiskIfc.Block) : M

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

  lemma ProcessReadPreservesInv(disk_addr: nat, data: DiskIfc.Block, rest: M)
  requires Inv(dot(DiskReadReq(disk_addr), rest))
  ensures Inv(dot(DiskReadResp(disk_addr, data), rest))

  lemma ProcessWritePreservesInv(disk_addr: nat, data: DiskIfc.Block, rest: M)
  requires Inv(dot(DiskWriteReq(disk_addr, data), rest))
  ensures Inv(dot(DiskWriteResp(disk_addr), rest))

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

module CrashAsyncIfc(ifc: InputOutputIfc) refines Ifc {
  import opened RequestIds

  datatype Op =
    | Start(rid: RequestId, input: ifc.Input)
    | End(rid: RequestId, output: ifc.Output)
    | InternalOp
    | CrashOp
}

module AsyncDiskSystemStateMachine(IOIfc: InputOutputIfc, ssm: DiskSSM(IOIfc))
    refines StateMachine(CrashAsyncIfc(IOIfc))
{
  import AsyncIfc = AsyncIfc(IOIfc)
  import Disk = AsyncDisk
  import opened DiskIfc
  import opened RequestIds

  datatype Variables = Variables(
      disk: Disk.Variables,
      machine: ssm.M)

  predicate Init(s: Variables) {
    && Disk.Init(s.disk)
    && ssm.Init(s.machine)
  }

  /*predicate InternalNext(s: Variables, s': Variables,
      shard: Variables, shard': Variables, rest: Variables)
  {
    && s == ssm.dot(shard, rest)
    && s' == ssm.dot(shard', rest)
    && ssm.Internal(shard, shard')
  }*/

  predicate Crash(s: Variables, s': Variables)
  {
    && Disk.Crash(s.disk, s'.disk)
    && ssm.Init(s'.machine)
  }

  datatype Step =
    | MachineStep(shard: ssm.M, shard': ssm.M, rest: ssm.M)
    | InteractionStep(dop: DiskOp)
    | DiskInternalStep

  predicate Machine(s: Variables, s': Variables, shard: ssm.M, shard': ssm.M, rest: ssm.M) {
    && ssm.Internal(shard, shard')
    && s.machine == ssm.dot(shard, rest)
    && s'.machine == ssm.dot(shard', rest)
    && s'.disk == s.disk
  }

  predicate DiskInternal(s: Variables, s': Variables) {
    && s.machine == s'.machine
    && Disk.NextInternal(s.disk, s'.disk)
  }

  predicate MachineInteraction(s: ssm.M, s': ssm.M, dop: DiskOp) {
    match dop {
      case ReqReadOp(id, reqRead) =>
        s == ssm.dot(s', ssm.DiskReadReq(reqRead.addr))

      case ReqWriteOp(id, reqWrite) =>
        s == ssm.dot(s', ssm.DiskWriteReq(reqWrite.addr, reqWrite.data))

      case RespReadOp(id, respRead) =>
        s' == ssm.dot(s, ssm.DiskReadResp(respRead.addr, respRead.data))

      case RespWriteOp(id, respWrite) =>
        s' == ssm.dot(s, ssm.DiskWriteResp(respWrite.addr))
    }
  }

  predicate Interaction(s: Variables, s': Variables, dop: DiskOp) {
    && Disk.Next(s.disk, s'.disk, dop)
    && MachineInteraction(s.machine, s'.machine, dop)
  }

  predicate InternalStep(s: Variables, s': Variables, step: Step)
  {
    match step {
      case MachineStep(shard, shard', rest) => Machine(s, s', shard, shard', rest)
      case InteractionStep(dop) => Interaction(s, s', dop)
      case DiskInternalStep => DiskInternal(s, s')
    }
  }

  predicate Internal(s: Variables, s': Variables)
  {
    exists step :: InternalStep(s, s', step)
  }

  predicate NewTicket(s: Variables, s': Variables, rid: RequestId, input: IOIfc.Input)
  {
    && ssm.NewTicket(s.machine, s'.machine, rid, input)
    && s.disk == s'.disk
  }

  predicate ConsumeStub(s: Variables, s': Variables, rid: RequestId, output: IOIfc.Output)
  {
    && ssm.ConsumeStub(s.machine, s'.machine, rid, output)
    && s.disk == s'.disk
  }

  predicate Next(s: Variables, s': Variables, op: ifc.Op) {
    match op {
      case Start(rid, input) => NewTicket(s, s', rid, input)
      case End(rid, output) => ConsumeStub(s, s', rid, output)
      case CrashOp => Crash(s, s')
      case InternalOp => Internal(s, s')
    }
  }
}

module DiskSSMTokens(ioifc: InputOutputIfc, ssm: DiskSSM(ioifc)) {
  //import pcm = SSM_PCM(ssm)
  //import Tokens = Tokens(pcm)

  //type Token = Tokens.Token
  datatype Token = Token(val: ssm.M)

  /*lemma transition_of_next(a: ssm.M, b: ssm.M)
  requires ssm.Next(a, b)
  ensures pcm.transition(a, b)
  {
    ssm.dot_unit(a);
    ssm.dot_unit(b);
    var a' := a;
    var b' := b;
    var c := ssm.unit();
    assert a == ssm.dot(a', c) && b == ssm.dot(b', c) && ssm.Next(a', b');
    assert pcm.single_step_helper(a, b, a', b', c);
    assert pcm.single_step(a, b);
  }

  lemma transition_of_next_with_unit(a: ssm.M, b: ssm.M)
  requires ssm.Next(a, b)
  ensures pcm.transition(pcm.dot(ssm.unit(), a), pcm.dot(ssm.unit(), b))
  {
    ssm.dot_unit(a);
    ssm.dot_unit(b);
    ssm.commutative(a, ssm.unit());
    ssm.commutative(b, ssm.unit());
    transition_of_next(a, b);
  }*/

  /*function method {:opaque} update_next(glinear a: Token, ghost expect_b: ssm.M)
      : (glinear b: Token)
  requires ssm.Next(a.val, expect_b)
  ensures b == Tokens.Token(a.loc, expect_b)
  {
    transition_of_next_with_unit(a.val, expect_b);
    Tokens.transition_update(Tokens.get_unit_shared(a.loc), a, expect_b)
  }*/

  // TODO more stuff here ...
}

/*
module Obligations(
    IOIfc: InputOutputIfc,
    ssm: TicketStubSSM(IOIfc),
    spec: StateMachine(IOIfc),
    ref: Refinement(
          AsyncIfc(IOIfc),
          TicketStubStateMachine(IOIfc, ssm),
          AsyncStateMachine(IOIfc, spec)
       )
  )
{ }
*/
