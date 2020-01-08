include "../MapSpec/ThreeStateVersioned.s.dfy"
include "PivotBetree.i.dfy"
include "PivotBetree_Refines_Betree.i.dfy"
//
// Defines a 3-state instantiation PivotBetree. That is, defines what state a disk can return to
// if the storage system (a PivotBetree) crashes.
//

module ThreeStateVersionedPivotBetree refines ThreeStateVersioned {
  import SM = PivotBetree
  import SM_Inv = PivotBetreeInvAndRefinement

  predicate Inv(k: Constants, s: Variables)
  {
    && SM_Inv.Inv(k.k, s.s1)
    && SM_Inv.Inv(k.k, s.s2)
    && SM_Inv.Inv(k.k, s.s3)
  }
}
