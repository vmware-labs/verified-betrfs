include "../MapSpec/MapSpec.s.dfy"
include "Tristate.i.dfy"

module TriStateMap refines TriState {
  import SM = MapSpec
}
