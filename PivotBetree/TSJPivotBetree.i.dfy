include "../MapSpec/TSJ.i.dfy"
include "PivotBetree.i.dfy"
include "PivotBetree_Refines_Betree.i.dfy"

//
// Defines a 3-state instantiation PivotBetree. That is, defines what state a disk can return to
// if the storage system (a PivotBetree) crashes.
//

module TSJPivotBetree refines TSJ {
  import SM = PivotBetree
}
