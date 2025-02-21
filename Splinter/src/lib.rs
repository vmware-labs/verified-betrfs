// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![verifier::loop_isolation(false)]

mod abstract_system;
mod allocation_layer;
mod betree;
mod disk;
mod journal;
// mod marshalling;
mod spec;
mod exec;

fn main() {}
