// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

// XXX --- QUESTION: Is this a module that just allocates disk blocks?
module AllocationMod {
  type AU = nat
  datatype CU = CU(au: AU, offset: nat)
  type UninterpretedDiskPage

  function DiskSizeInAU() : (s:nat)
    ensures 1<=s

  function AUSizeInCUs() : (s:nat)
    ensures 2<=s  // TODO(jonh): explain why

  function {:opaque} CUsInDisk() : set<CU>
  {
    set au,offset | 0<=au<DiskSizeInAU() && 0<=offset<AUSizeInCUs() :: CU(au,offset)
  }

  predicate ValidCU(cu: CU) {
    && 0 <= cu.au < DiskSizeInAU()
    && 0 <= cu.offset < AUSizeInCUs()
  }

  type DiskView = map<CU, UninterpretedDiskPage>

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

  // TODO: this should probably be defined over CUs.
  // Sowmya: I think this TODO is done?
  predicate DiskViewsEquivalentForSet(dv0: DiskView, dv1: DiskView, cus: seq<CU>)
  {
    forall cu :: cu in cus ==> EqualAt(dv0, dv1, cu)
  }
}
