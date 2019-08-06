include "ThreeStateVersioned.s.dfy"
include "PivotBetree.i.dfy"

module ThreeStateVersionedPivotBetree refines ThreeStateVersioned {
  import SM = PivotBetree
}
