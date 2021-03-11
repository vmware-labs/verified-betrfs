// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PivotBetree.i.dfy"
include "../Versions/StatesView.i.dfy"

module StatesViewPivotBetree refines StatesView {
  import SM = PivotBetree
}
