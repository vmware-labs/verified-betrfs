include "ThreeStateVersioned.dfy"
include "MapSpec.dfy"

module ThreeStateVersionedMap refines ThreeStateVersioned {
  import SM = MapSpec
}
