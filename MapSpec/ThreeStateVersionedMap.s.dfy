// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "../MapSpec/ThreeStateVersioned.s.dfy"
include "../MapSpec/MapSpec.s.dfy"

module ThreeStateVersionedMap refines ThreeStateVersioned {
  import SM = MapSpec
}
