// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause


include "basics.dfy"
include "delete.dfy"
include "insert.dfy"
include "lemmas.dfy"
include "node.dfy"
include "splay.dfy"
include "zig_right.dfy"
include "zig_left.dfy"

newtype{:nativeType "uint"} uint32 = i:int | 0 <= i < 0x100000000
newtype{:nativeType "ulong"} uint64 = i:int | 0 <= i < 0x10000000000000000
