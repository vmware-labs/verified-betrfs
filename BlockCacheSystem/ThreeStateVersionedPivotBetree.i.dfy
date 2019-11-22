include "../MapSpec/ThreeStateVersioned.s.dfy"
include "../PivotBetree/PivotBetree.i.dfy"
//
// Defines a 3-state instantiation PivotBetree. That is, defines what state a disk can return to
// if the storage system (a PivotBetree) crashes.
//

module ThreeStateVersionedPivotBetree refines ThreeStateVersioned {
  import SM = PivotBetree
}
