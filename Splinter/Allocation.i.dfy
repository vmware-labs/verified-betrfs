include "DiskTypes.s.dfy"

// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

// XXX --- QUESTION: Is this a module that just allocates disk blocks?
module AllocationMod {
  import opened DiskTypesMod

  // TODO(jonh): robj points out we should have a ValidView first, then fullness later.
  predicate FullView(dv: DiskView) {
    forall cu :: cu in dv.Keys <==> ValidCU(cu)
  }

  predicate Empty(dv: DiskView) {
    dv.Keys == {}
  }

  predicate EqualAt(dv0: DiskView, dv1: DiskView, cu: CU)
  {
    || (cu !in dv0 && cu !in dv1)
    || (cu in dv0 && cu in dv1 && dv0[cu]==dv1[cu])
  }

  // TODO : cleanup this interface -- we can get rid of this
  predicate DiskViewsEquivalent(dv0: DiskView, dv1: DiskView, cus: set<CU>)
  {
    forall cu :: cu in cus ==> EqualAt(dv0, dv1, cu)
  }

  predicate DiskViewsEquivalentForSeq(dv0: DiskView, dv1: DiskView, cus: seq<CU>)
  {
    forall cu :: cu in cus ==> EqualAt(dv0, dv1, cu)
  }



}
