include "ThreeStateVersioned.s.dfy"
include "MapSpec.s.dfy"

module ThreeStateVersionedMap refines ThreeStateVersioned {
  import SM = MapSpec
}
