abstract module UIOpIfc {
  // transition labels enforce correspondence between low-level trusted ABI & upper-level semantics
  type UIOp(!new,==)
}

abstract module StateMachineIfc(uiopifc: UIOpIfc) {
  type Constants(!new,==)
  type Variables(!new,==)

  predicate Init(c: Constants, v: Variables)

  predicate Next(c: Constants, v: Variables, v': Variables, uiop: uiopifc.UIOp)
}

abstract module RefinesIfc(
  uiopifc: UIOpIfc, lower: StateMachineIfc(uiopifc), upper: StateMachineIfc(uiopifc)) {
  function Iconstants(lc: lower.Constants) : (uc: upper.Constants)

  function I(lc: lower.Constants, lv: lower.Variables) : (uv: upper.Variables)

  // Give the prover an opprotunity to constrain the state space over which refinement works.
  // In TLA terms, we're enabling this proof strategy: Init && []Next ==> []Inv ==> []Refines
  predicate Inv(lc: lower.Constants, lv: lower.Variables)

  // That Inv-constrained state space has to be big enough to include all valid lower-behaviors
  lemma InvInductive(lc: lower.Constants, lv: lower.Variables, lv': lower.Variables, uiop: uiopifc.UIOp)
    ensures lower.Init(lc, lv) ==> Inv(lc, lv)
    ensures Inv(lc, lv) && lower.Next(lc, lv, lv', uiop) ==> Inv(lc, lv')

  // Every time the lower machine takes a next step labeled with uiop, the upper state machine
  // takes a correspondingly-labeled step.
  lemma Refines(lc: lower.Constants, lv: lower.Variables, lv': lower.Variables, uiop: uiopifc.UIOp)
    ensures Inv(lc, lv) && lower.Next(lc, lv, lv', uiop)
      ==> upper.Next(Iconstants(lc), I(lc, lv), I(lc, lv'), uiop)
}

// For now, while we're only going down into atomic state machines, we want to prove
// statements of this form:
//module ImplementationObligation(implementation: StateMachineIfc) refines RefinesIfc(CrashTolerantUIOp(MapSpec), implementation, CrashTolerantMapSpecMod ) {}

// Eventually, we'll have some .s runtime framework for a single-threaded event loop.
// That framework will require refinement from the heap states to the top-level state
// machine, and it'll be placed correctly to enforce uiop correpsondence.
//module MainIfc(implStateMachine: ) {
//  function Iconstants() 
//
//  function Iheap() 
//    reads *
//
//  method setup()
//    ensures 
//
//  method handle()
//}

//module ImplementationObligation(implementation: MainIfc) refines RefinesIfc(implementation, CrashTolerantMapSpecMod) { }

// Build system will enforce this single line, the one line that is both trusted
// and includes the implementation by reference.
// Notice that this line can be used by every instance of this methodology:
// RefinementObligation is defined by "player one" (in a trusted .s file);
// Main is defined by "player two" (in a verified file tree).
//module ConcreteRefinementObligation refines ImplementationObligation(Main)
