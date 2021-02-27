// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "PivotBetree.i.dfy"
include "../Versions/StatesView.i.dfy"

module StatesViewPivotBetree refines StatesView {
  import SM = PivotBetree
}
