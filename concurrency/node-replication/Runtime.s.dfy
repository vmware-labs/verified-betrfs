// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

module {:extern "LinearExtern"} Runtime {
  method {:extern "LinearExtern", "CurrentNumaNode"} CurrentNumaNode()
    returns (node: nat) // Well this probably should be u64 but don't know what to include
    ensures node < 4 as nat // Who needs more than 4 numa nodes?
}