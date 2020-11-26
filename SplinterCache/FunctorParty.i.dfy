abstract module UIfc {
  type UIOp(==)
}

abstract module UIStateMachine(Ifc:UIfc) {
  type Vars(==, !new)
  predicate Init(s:Vars)
  predicate Next(s:Vars, s':Vars, uiop:Ifc.UIOp)
}

// The "unwinding condition" necessary to prove the TLA expression:
// L.Init && []L.Next ==> H.Init && []H.Next
abstract module StateMachinesRefine(L:UIStateMachine, H:UIStateMachine) {

  // Implementation must supply an interpretation function.
  function I(s:L.Vars) : H.Vars

  // Implementation provides an invariant to support induction.
  predicate Inv(s:L.Vars)

  lemma InterpPreservesInit(s:L.Vars)
      requires L.Init(s)
      ensures H.Init(I(s))

  lemma InvInit(s:L.Vars)
      requires L.Init(s)
      ensures Inv(s)

  lemma InvNext(s:L.Vars, s':L.Vars)
      requires Inv(s)
      requires L.Next(s, s')
      ensures Inv(s')
      ensures H.Next(I(s), I(s'))
}

module CacheClientProgram(Ifc : UIOp) {
  type Vars(==, !new)
  predicate Init(s:Vars)
  predicate Next(s:Vars, s':Vars, uiop:Ifc.UIOp, cop:CacheOp)
}

// Run the program directly against the Disk interface, without a cache.
// Assumes we can magically synthesize atomic writes, so we have to skip over
// the IOSystem.
// XXX yeah and dop is going to allow multiple ops, but then *DISallow* them in the IOSystem.
// XXX Gonna need to parameterize the disk's block type at some point.

module DirectStorageSystem(Client : CacheClientProgram)
  refines UIStateMachine(Ifc = Client.Ifc)
{
  datatype Vars = Vars(c: Client.Vars, d: Disk.Vars)

  predicate Init(s:Vars)
  {
    && Client.Init(s.c)
    && Client.Mkfs(s.d)
  }

  predicate Next(s:Vars, s':Vars, uiop:Ifc.UIOp)
  {
    exists dop ::
    && Client.Next(s.c, s'.c, uiop, dop)
    && Disk.Next(s.d, s'.d, dop)
  }
}

abstract module BlockType {
  type Block(==)
}

abstract module BlockIfc(B : BlockType) {
  type Addr(==)
  datatype SingletonBlockOp = Read(a:Addr, b:B) | Write(a:Addr, b:B)
  datatype BlockOp = seq<SingletonBlockOp>

  // IOSystem demands that IOs be one-at-a-time to make room for crashes.
  SingleIO(dop:BlockOp) { |dop| == 1 }
}

abstract module DiskProgram(Ifc : UIfc, B : BlockType) {
  import BlockIfc(B = B)

  type Vars(==, !new)
  // TODO could we declare that type Vars has these predicates as namespace predicates? That'd be keen.
  predicate Init(s:Vars)
  predicate Next(s:Vars, s':Vars, uiop:Ifc.UIOp, dop:BlockOp)
}

// XXX there are a few ways we could do this:
//  * CacheClientProgram and CacheImpl are complete state machines tied together
//    with a binding variable in a wrapper compound state machine,
//    CachedStorageSystem. That's what I'm doing here.
//  * CacheImpl takes CacheClientProgram as a module argument. We could get away
//    with that here, using placeholder program modules so we could reason about
//    the cache in the abstract. This is analogous to how the current system works,
//    and is a little unsatisfyingly asymmetrical. It does remove one state machine
//    from the soup.
//  * CacheClientProgram takes CacheImpl as an argument. I think this is the worst of
//    all worlds. Right now, we need to plug program into a cacheless DirectStorageSystem;
//    there'd be no way to do that here. And it's asymmetrical.
// So I think the way I've got it here is the goal.

// XXX Do we need to offer different up vs down BlockTypes?
abstract module CacheImpl(B : BlockType) {
  type Vars(==, !new)
  // TODO could we declare that type Vars has these predicates as namespace predicates? That'd be keen.
  predicate Init(s:Vars)
  predicate Next(s:Vars, s':Vars, cop:BlockOp, dop:BlockOp)
}

abstract module CachedStorageSystem(Client : CacheClientProgram, Cache : CacheImpl)
  refines DiskProgram(Ifc = Client.Ifc, B = Cache.BlockType)
{
  datatype Vars = Vars(p: Client.Vars, c: Cache.Vars)

  predicate Init(s:Vars) {
    && Client.Init(s.p)
    && Cache.Init(s.c)
  }

  predicate Next(s:Vars, s':Vars, uiop:Ifc.UIOp, dop:BlockOp)
  {
    // Might want a special case for "cache does a thing, client stutters".
    exists cop:BlockOp ::
      && Client.Next(s.p, s'.p, cop)
      && Cache.Next(s.c, s'.c, cop, dop)
  }
}

module IOSystem(Program : DiskProgram)
  refines UIStateMachine(Ifc = Program.Client.Ifc)
{
  datatype Vars = Vars(p: Program.Vars, d: Disk.Vars)

  predicate Init(s:Vars)
  {
    && Program.Init(s.p)
    && Program.Mkfs(s.d)
  }

  predicate Next(s:Vars, s':Vars, uiop:Ifc.UIOp)
  {
    // XXX add crash steps
    exists dop ::
    && SingleIO(dop)
    && Program.Next(s.p, s'.p, uiop, dop)
    && Disk.Next(s.d, s'.d, dop)
  }
}

// This is just the StateMachineRefines obligation, typed specifically for the structure
// of our system, plugging in a trusted Disk/IOSystem, and inside that a ThruCcahe
// that's a placeholder for plugging in a CrashSafeCache later.
abstract module CachedStorageSystemImplementsSpec(X:CacheClientProgram, Y:UIStateMachine)
    refines StateMachinesRefine(
        L = DirectStorageSystem(CacheClient = X),
        H = Y)
{ }

module Betree refines CacheClientProgram(Ifc = Map)
{
  // ... XXX add implementation
}

module BetreeImplementsMap refines CachedStorageSystemImplementsSpec(X = Betree, Y = Map)
{
   // ... XXX supply here a proof to show this specific refinement.
}

module CrashSafeCache(B : BlockType) refines CacheImpl(B = B)
{
  // ... XXX add implementation
}

// This module proves that CrashSafeCache converts a data structure into a crash safe data
// structure.
// Spefically, it proves a refinement (satisfies StateMachinesRefine) that
// X+CrashSafeCache implements CrashSafe<Y>, given a proof that X+ThruCache
// implements Y
module CrashSafeCacheProvidesCrashSafety(
  X:CacheClientProgram, Y:UIStateMachine, Antecedent:CachedStorageSystemImplementsSpec(X, Y))
  refines StateMachinesRefine(
    L = IOSystem(
      DiskProgram = CachedStorageSystem(CacheClient = X, Cache = CrashSafeCache),
      Disk = Disk),
    H = CrashSafe(Spec = Y)
{
   // ... XXX supply here a proof to show the refinement. Call into Antecedent to get necessary lemmas.
}

// .s This is the climax of the system. Build system demands that it be instantiatied
// as a non-abstract module, hence supplying a proof.
abstract module SystemTheorem(
  Proof : StateMachinesRefine(
    L = IOSystem(
      DiskProgram = CachedStorageSystem(CacheClient = Betree, Cache = CrashSafeCache),
      Disk = Disk),
    H = CrashSafe(Spec = Map)))

// The proof is easy; just apply CrashSafeCacheProvidesCrashSafety.
// This module declaration (with empty body) *is* the entire proof.
module SystemProof refines SystemTheorem(
  Proof = CrashSafeCacheProvidesCrashSafety(
    X = Betree,
    Y = Map,
    Antecedent = BetreeImplementsMap))
