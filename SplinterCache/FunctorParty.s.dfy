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
abstract module StateMachinesRefine(Ifc: UIfc, L:UIStateMachine(Ifc), H:UIStateMachine(Ifc)) {

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

// This module is just a type-template parameter placeholder.
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

// TODOiscuss with chris: Having to cart around every parameter required by
// higher-level modules is tedious; it reeks of D<B<A>, C> nonsense in
// templateland. Would some sort of module-synonym mechanism let us stop doing
// this? Or should we consider trying to mix these functors with "import :"
// type abstraction from Dafny (which still confuses me easily)? I mean, it
// SHOULD help, because instead of a takes-a relation, we'd use a has-a relation.
// Happy to try it, but suspicious we'll be unable to fill in those holes later
// to make them match other parameters. Try it with me?
module IOSystem(Ifc: Ifc, B: BlockType, Program : DiskProgram(Ifc, B))
  refines UIStateMachine(Ifc = Ifc)
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


// .s This is the climax of the system. Build system demands that it be instantiatied
// as a non-abstract module, hence supplying a proof.
abstract module SystemTheorem(
  Ifc: UIfc, B: BlockType, P: DiskProgram(Ifc = Ifc, B = B), CrashSafeSpec: UIStateMachine(Ifc = Ifc),
  Proof : StateMachinesRefine(
    L = IOSystem(DiskProgram = P),
    H = CrashSafeSpec)))

//////////////////////////////////////////////////////////////////////////////

// XXX TODO As written above, nothing forces CrashSafeSpec to actually be
// CrashSafe(Map), nor does anything force P to be
// CachedStorageSystem(CacheClient = Betree, Cache = CrashSafeCache).  Does
// that binding belong in a more-detailed theorem here in this .s, or is that a
// build-system constraint?
//
// Maybe the code above is a library .s file, and then another .s file would
// bring in Map and CrashSafe to provide the actual Theorem for our particular
// system.  The build system would be what demands the match between the impl
// and whatever spec we're offering in impl (Betree + CrashSafeCache).
