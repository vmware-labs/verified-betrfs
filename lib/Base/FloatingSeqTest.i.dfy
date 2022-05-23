// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "FloatingSeq.s.dfy"

module FloatingSeqTest {
  import opened FloatingSeqMod

  lemma tests()
  {
    var a := FloatingSeq(0, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    assert a.Len()==11;

    var b := FloatingSeq(8, [8, 9, 10]);
    assert b.Len()==11;
  
    assert a.GetSuffix(8) == b;

    assert a.Get(9) == 9;
    assert b.Get(9) == 9;
    assert a.Get(3) == 3;
    //assert b.Get(3) == 3; // fails requirement; b has forgotten idx 3

    assert b.GetPrefix(9) == FloatingSeq(8, [8]);
    assert b.Append([11, 12]) == a.Append([11, 12]).GetSuffix(8);
  }
}
