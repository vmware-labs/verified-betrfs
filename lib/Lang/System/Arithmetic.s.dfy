// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../NativeTypes.s.dfy"

// unsigned integer addition with overflow allowed

module {:extern} NativeArithmetic {
  import opened NativeTypes

  function method {:extern "NativeArithmetic_Compile", "u64add" }
  u64add(a: uint64, b: uint64) : (c : uint64)
  ensures c as int == (
    if a as int + b as int < 0x1_0000_0000_0000_0000 then
      a as int + b as int
    else
      a as int + b as int - 0x1_0000_0000_0000_0000
  )
}
