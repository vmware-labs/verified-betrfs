// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../MapSpec/MapSpec.s.dfy"
include "StatesView.i.dfy"

module StatesViewMap refines StatesView {
  import SM = MapSpec
}
