// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Betree/BlockInterface.i.dfy"
include "PivotBetreeGraph.i.dfy"

module PivotBetreeBlockInterface refines BlockInterface {
  import G = PivotBetreeGraph
}
