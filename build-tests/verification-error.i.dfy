// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

// This file produces a failure during verification.
lemma foo()
    ensures 8 < 7
{
}
