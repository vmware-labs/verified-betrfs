// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

// This file produces a failure during verification.
lemma foo()
    ensures 7 < 8
{
}
