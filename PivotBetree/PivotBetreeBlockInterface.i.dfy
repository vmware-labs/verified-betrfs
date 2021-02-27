// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "../Betree/BlockInterface.i.dfy"
include "PivotBetreeGraph.i.dfy"

module PivotBetreeBlockInterface refines BlockInterface {
  import G = PivotBetreeGraph
}
