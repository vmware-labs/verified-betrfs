include "PivotBetree.i.dfy"
include "../Versions/StatesView.i.dfy"

module StatesViewPivotBetree refines StatesView {
  import SM = PivotBetree
}
