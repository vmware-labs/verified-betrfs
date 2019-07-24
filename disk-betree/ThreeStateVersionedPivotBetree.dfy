include "ThreeStateVersioned.dfy"
include "PivotBetree.dfy"

module ThreeStateVersionedPivotBetree refines ThreeStateVersioned {
  import SM = PivotBetree
}
