// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "../Betree/BlockInterface.i.dfy"
include "PivotBetreeGraph.i.dfy"

module PivotBetreeBlockInterface refines BlockInterface {
  import G = PivotBetreeGraph
}
