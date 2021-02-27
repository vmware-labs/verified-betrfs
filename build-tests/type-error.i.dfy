// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

// This file produces a failure during type checking.
predicate foo(x:int) { true }

method bar() {
    foo(7, 7);
}
