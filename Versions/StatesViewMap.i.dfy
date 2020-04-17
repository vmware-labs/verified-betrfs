include "../MapSpec/MapSpec.s.dfy"
include "StatesView.i.dfy"

module StatesViewMap refines StatesView {
  import SM = MapSpec
}
