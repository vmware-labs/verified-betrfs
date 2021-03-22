// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../MapSpec/ThreeStateVersioned.s.dfy"
include "../MapSpec/MapSpec.s.dfy"

module ThreeStateVersionedMap refines ThreeStateVersioned {
  import SM = MapSpec
}
