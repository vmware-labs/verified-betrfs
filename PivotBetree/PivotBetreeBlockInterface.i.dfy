include "../Betree/BlockInterface.i.dfy"
include "PivotBetreeGraph.i.dfy"

module PivotBetreeBlockInterface refines BlockInterface {
  import G = PivotBetreeGraph
}
