include "../MapSpec/ThreeStateVersioned.s.dfy"
include "../MapSpec/MapSpec.s.dfy"

module ThreeStateVersionedMap refines ThreeStateVersioned {
  import SM = MapSpec
}
