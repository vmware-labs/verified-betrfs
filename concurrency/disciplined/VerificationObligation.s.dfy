include "AsyncAppSpec.s.dfy"
include "ConcurrencyModel.s.dfy"

// This is the ultimate verification theorem statement. This module brings
// together a set of obligations. If the build system verifies a module
// satisfies these obligations (completely refines this module), then
// the executable associated with that module implements the system
// specification.

abstract module VerificationObligation {
  import AsyncSpec // The async spec as instantiated with the specific application
  //import MapSpec	// TODO this should be a module application <A:AppSpec>
  import Ifc = MapIfc
  import SSM : ShardedStateMachine //	from ConcurrencyModel
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

  // Implementer is obliged to provide an interpretation function from SSM
  // variables TO SPec variables. TODO: how can this not go through SSM!?
  function I(s: SSM.Variables) : AsyncSpec.Variables

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
    requires SSM.Valid(s)
    requires SSM.Internal(s, s')  // Transitions of the sharded state machine ...
    ensures SSM.Valid(s')
    ensures AsyncSpec.Next(I(s), I(s'), AsyncSpec.Ifc.InternalOp) // ... induce valid transitions of the AsyncSpec.

  // PhysicalIfc (bottom bread)
  //
  // This section defines the (implementation-level) interfaces
  // to the outside world.
  type Variables(==,!new) // using this name so the impl is more readable
  predicate Inv(v: Variables)

  method init(glinear in_sv: SSM.Variables)
  returns (v: Variables, glinear out_sv: SSM.Variables)
  requires SSM.Init(in_sv)
  ensures Inv(v)

  // The whole point of using this VerificationObligations.s file is that, in return
  // for meeting its constraints, its main() invokes this call() method on many
  // threads concurrently.
  method call(v: Variables, input: Ifc.Input,
      rid: int, glinear in_sv: SSM.Variables, thread_id: uint32)
  returns (output: Ifc.Output, glinear out_sv: SSM.Variables)
  decreases * // boi I don't feel bad about this
  requires Inv(v)
  requires in_sv == SSM.input_ticket(rid, input)
  ensures out_sv == SSM.output_stub(rid, output)

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
  lemma NewTicket_RefinesMap(s: SSM.Variables, s': SSM.Variables, rid: int, input: Ifc.Input)
    requires SSM.Valid(s) // TODO(travis): was Inv, but Valid is correct here, surely?
    requires SSM.NewTicket(s, s', rid, input)
    ensures SSM.Valid(s')
    ensures AsyncSpec.Next(I(s), I(s'), AsyncSpec.Ifc.Start(rid, input))

  // Consuming a stub corresponds to an atomic AsyncSpec step that returns the
  // response (with the same input value) to the client.
  lemma ReturnStub_RefinesMap(s: SSM.Variables, s': SSM.Variables, rid: int, output: Ifc.Output)
    requires SSM.Valid(s)
    requires SSM.ReturnStub(s, s', rid, output)
    ensures SSM.Valid(s')
    ensures AsyncSpec.Next(I(s), I(s'), AsyncSpec.Ifc.End(rid, output))

// Libraries the app is allowed to use. Without it, you get concurrency, but no
// communication between threads. With a Mutex, threads can communicate through
// lock-protected shared memory.
//	ConcurrencyTools (Mutex)
}
