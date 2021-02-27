// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "../lib/sequences.dfy"
include "../lib/NativeTypes.dfy"

module Main {
  import opened Sequences;
  import opened NativeTypes;

  method Main() {
    var s := Range(40000);

    var k: uint64 := 0;
    while k < 10 {
      var i: uint64 := 0;
      while i < 20000
      {
        var slice := s[i..i+20000];
        i := i + 1;
      }
      k := k + 1;
    }
  }
}

