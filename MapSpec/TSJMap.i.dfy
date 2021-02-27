// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "../MapSpec/TSJ.i.dfy"
include "../MapSpec/MapSpec.s.dfy"

module TSJMap refines TSJ {
  import SM = MapSpec
}
