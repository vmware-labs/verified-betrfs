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
    | Start(ghost rid: RequestId, input: ifc.Input)
    | End(ghost rid: RequestId, output: ifc.Output)
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

module DiskPCM(IOIfc: InputOutputIfc,
  ssm: DiskSSM(IOIfc)) refines PCM {
  
  type M = ssm.M

  function dot(x: M, y: M) : M
  {
    ssm.dot(x, y)
  }

  predicate valid(x: M)
  {
    exists y: M :: ssm.Inv(dot(x, y))
  }

  function unit(): M
  {
    ssm.unit()
  }

  lemma dot_unit(x: M)
  {
    ssm.dot_unit(x);
  }

  lemma valid_unit(x: M)
  {
    var x := ssm.exists_inv_state();
    commutative(unit(), x);
    dot_unit(x);
    assert ssm.Inv(dot(unit(), x));
  }

  lemma commutative(x: M, y: M)
  //ensures dot(x, y) == dot(y, x)
  {
    ssm.commutative(x, y);
  }

  lemma associative(x: M, y: M, z: M)
  //ensures dot(x, dot(y, z)) == dot(dot(x, y), z)
  {
    ssm.associative(x, y, z);
  }

  predicate single_step_helper(a: M, b: M, a': M, b': M, c: M) {
    a == dot(a', c) && b == dot(b', c) && ssm.Internal(a', b')
  }

  predicate single_step(a: M, b: M) {
    exists a', b', c :: single_step_helper(a, b, a', b', c)
  }

  least predicate reachable(a: M, b: M) {
    a == b || (exists z :: reachable(a, z) && single_step(z, b))
  }

  predicate transition(a: M, b: M) {
    reachable(a, b)
  }

  lemma transition_is_refl(a: M)
  //requires transition(a, a)
  {
  }

  least lemma reachable_is_trans(a: M, b: M, c: M)
  requires reachable(b, c)
  requires transition(a, b)
  ensures reachable(a, c)
  {
    if b == c {
    } else {
      var z :| reachable(b, z) && single_step(z, c);
      reachable_is_trans(a, b, z);
    }
  }

  lemma transition_is_trans(a: M, b: M, c: M)
  //requires transition(a, b)
  //requires transition(b, c)
  ensures transition(a, c)
  {
    reachable_is_trans(a, b, c);
  }

  least lemma reachable_is_monotonic(a: M, b: M, c: M)
  requires reachable(a, b)
  ensures reachable(dot(a, c), dot(b, c))
  {
    if a == b {
    } else {
      var z :| reachable(a, z) && single_step(z, b);
      reachable_is_monotonic(a, z, c);
      var z', b', d :| single_step_helper(z, b, z', b', d);
      associative(z', d, c);
      associative(b', d, c);
      assert single_step_helper(dot(z, c), dot(b, c), z', b', dot(d, c));
      assert single_step(dot(z, c), dot(b, c));
    }
  }

  lemma transition_is_monotonic(a: M, b: M, c: M)
  //requires transition(a, b)
  ensures transition(dot(a, c), dot(b, c))
  {
    reachable_is_monotonic(a, b, c);
  }
}

module DiskSingletonLoc {
  import opened GhostLoc
  function {:extern} loc(): Loc
}

module DiskToken(IOIfc: InputOutputIfc, ssm: DiskSSM(IOIfc)) {
  import pcm = DiskPCM(IOIfc, ssm)
  import Tokens = Tokens(pcm)
  import opened DiskSingletonLoc

  datatype {:glinear_fold} Token = Token(val: ssm.M)
  {
    function defn() : Tokens.Token {
      Tokens.Token(loc(), val)
    }
  }
}
