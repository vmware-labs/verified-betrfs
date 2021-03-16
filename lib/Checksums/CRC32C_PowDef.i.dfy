// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Lang/System/F2_X.s.dfy"

module CRC32C_PowDef {
  import opened Bits_s
  import opened F2_X_s
  import opened NativeTypes

  function pow_mod_crc(n: nat) : seq<bool>
  requires n >= 33
  {
    reverse(mod_F2_X(zeroes(n-33) + [true], bits_of_int(0x1_1EDC_6F41, 33)))
  }
}
