// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "../MapSpec/MapSpec.s.dfy"
include "StatesView.i.dfy"

module StatesViewMap refines StatesView {
  import SM = MapSpec
}
