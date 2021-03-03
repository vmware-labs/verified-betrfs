// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "../MapSpec/MapSpec.s.dfy"
include "StatesView.i.dfy"

module StatesViewMap refines StatesView {
  import SM = MapSpec
}
