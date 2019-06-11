include "MapSpec.dfy"
include "DiskBetree.dfy"
  
abstract module DiskBetreeInv {
  import opened DB : DiskBetree

  /// Invariants
  
  predicate Inv(k: Constants, s: Variables)
  {
    forall key | MS.InDomain(key) :: KeyHasSatisfyingLookup(k, s, key)
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
    assert forall key :: MS.InDomain(key) ==> IsSatisfyingLookup(k, s, key, MS.EmptyValue(), [Layer(BC.Root(k.bcc), EmptyNode(), [Insertion(MS.EmptyValue())])]);
  }

  lemma NextStepPreservesInvariant(k: Constants, s: Variables, s': Variables, step: Step)
    requires Inv(k, s)
    requires NextStep(k, s, s', step)
    ensures Inv(k, s')
    
  lemma NextPreservesInvariant(k: Constants, s: Variables, s': Variables)
    requires Inv(k, s)
    requires Next(k, s, s')
    ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', step);
    NextStepPreservesInvariant(k, s, s', step);
  }
    

}
