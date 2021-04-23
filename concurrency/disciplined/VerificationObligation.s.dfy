// This is the ultimate verification theorem statement. This module brings
// together a set of obligations. If the build system verifies a module
// satisfies these obligations (completely refines this module), then
// the executable associated with that module implements the system
// specification.

module VerificationObligation {
  import AsyncSpec // The async spec as instantiated with the specific application
  import Ifc = MapIfc
  import SSM : ShardedStateMachine
    // The burger. it's not bread (it's mostly supplied by the .i adversary),
    // but it does have to meet obligations so that it impedance-matches the
    // atomic-model of the AsyncSpec to the concurrent-model of the
    // PhysicalIfc.
    // The obligation is what permits the implementation to abstract away
    // fine-grained concurrency. In ShardedStateMachine land, that obligation
    // is to be a Partially-Commutative Monoid. In IronFleet (shared-nothing)
    // land, that obligation is the reduction obligation on sequencing of
    // network receieves and sends in a physical ifc event handler.
  import opened NativeTypes


  // AsyncSpec refinement (semantics) (top bread)
  //
  // Refinement to AsyncSpec ensures that, when we do return a response, the
  // value inside that response is constrained by the AsyncSpec state machine.
  // The implementation may advance its ShardedStateMachine by any "internal"
  // transition that refines to a non-interface transition in the AsyncSpec.
  // This may be a linearization point (that justifies replacement of a request
  // with a particular response in the AsyncSpec) or a no-op (work happening in
  // the sharded state machine that doesn't affect the interpretation to the
  // AsyncSpec).
  lemma Internal_RefinesMap(s: SSM.Variables, s': SSM.Variables)
    requires SSM.Inv(s)
    requires SSM.Internal(s, s')  // Transitions of the sharded state machine ...
    ensures SSM.Inv(s')
    ensures AsyncSpec.Next(I(s), I(s'), Ifc.InternalOp) // ... induce valid transitions of the AsyncSpec.

  // PhysicalIfc (bottom bread)
  //
  // This section defines the (implementation-level) interfaces
  // to the outside world.
  type Variables(==,!new) // using this name so the impl is more readable
  predicate Inv(v: Variables)

  method init(glinear in_r: SSM.R)
  returns (v: Variables, glinear out_r: SSM.R)
  requires SSM.Init(in_r)
  ensures Inv(v)

  method call(v: Variables, input: Ifc.Input,
      rid: int, glinear in_r: SSM.R, thread_id: uint32)
  returns (output: Ifc.Output, glinear out_r: SSM.R)
  decreases * // boi I don't feel bad about this
  requires Inv(v)
  requires in_r == SSM.input_ticket(rid, input)
  ensures out_r == SSM.output_stub(rid, output)

  // Correspondence (toothpick)
  //
  // ensures that the physical requests and replies
  // processed in the physical interface correspond to the expected application-spec
  // level transition labels. The physical interface binds every physical request
  // (resp. reply with an input value) to a ghost ticket (resp. stub with an
  // output value). These lemmas ensure that every invocation of call refines a
  // transition in the app spec, and in particular, a transition with the
  // matching (input, output) label.

  // Accepting a ticket corresponds to an atomic AsyncSpec step that recognizes
  // the arrival of the request (with the same input value).
  lemma NewTicket_RefinesMap(s: SSM.Variables, s': SSM.Variables, rid: int, input: MapIfc.Input)
    requires SSM.Inv(s)
    requires SSM.NewTicket(s, s', rid, input)
    ensures SSM.Inv(s')
    ensures AsyncSpec.Next(I(s), I(s'), Ifc.Start(rid, input))

  // Consuming a stub corresponds to an atomic AsyncSpec step that returns the
  // response (with the same input value) to the client.
  lemma ReturnStub_RefinesMap(s: SSM.Variables, s': SSM.Variables, rid: int, output: MapIfc.Output)
    requires SSM.Inv(s)
    requires SSM.ReturnStub(s, s', rid, output)
    ensures SSM.Inv(s')
    ensures AsyncSpec.Next(I(s), I(s'), Ifc.End(rid, output))


// Libraries the app is allowed to use
//	ConcurrencyModel (ResourceSpec)
//	ConcurrencyTools (Mutex)

	AsyncAppSpec
	PhysicalInterface // Main
  Correspondence // Connects phys ifc to AsyncAppIfc
}
