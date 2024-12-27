// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
pub mod spec;

// trusted outer thingy.
// This is the one file that breaks the "trusted things can't mention verified stuff" rule,
// because it's here that we're identifying a specific implementation that satisfies all
// the auditor's obligations.
pub fn main()
{
}
