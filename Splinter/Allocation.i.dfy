include "Base.s.dfy"

module AllocationMod {
  type AU = nat
  datatype CU = CU(au: AU, offset: nat)
  type UninterpretedDiskPage

  function DiskSizeInAU() : (s:nat)
    ensures 1<=s

  function AUSizeInCUs() : (s:nat)
    ensures 2<=s  // TODO(jonh): explain why

  predicate ValidCU(cu: CU) {
    && 0 <= cu.au < DiskSizeInAU()
    && 0 <= cu.offset < AUSizeInCUs()
  }

  type DiskView = map<CU, UninterpretedDiskPage>

  // TODO(jonh): robj points out we should have a ValidView first, then fullness later.
  predicate FullView(dv: DiskView) {
    forall cu :: cu in dv.Keys <==> ValidCU(cu)
  }

  predicate EqualAt(dv0: DiskView, dv1: DiskView, cu: CU)
  {
    || (cu !in dv0 && cu !in dv1)
    || (cu in dv0 && cu in dv1 && dv0[cu]==dv1[cu])
  }

  // TODO: this should probably be defined over CUs.
  predicate DiskViewsEquivalentForSet(dv0: DiskView, dv1: DiskView, aus: seq<AU>)
  {
    forall cu:CU :: cu.au in aus ==> EqualAt(dv0, dv1, cu)
  }
}

