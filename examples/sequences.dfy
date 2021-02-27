// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "../lib/sequences.s.dfy"

module Main {
  import opened Sequences;

  method Main() {
    var xs := [3, 5, 11, 8, 2, 44];
    var ys := Filter(x => x < 10, xs);
    assert forall i: nat :: i < |ys| ==> ys[i] < 10;
    print ys;
  }
}
