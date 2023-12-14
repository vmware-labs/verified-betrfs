
module DiskTypesMod {
  type AU = nat
  // QUESTION: Can we add a clean/dirty bit here??
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

  function {:opaque} CUsInDisk() : set<CU>
    // This is the same as | ValidCU(), but written in a way to satisfy Dafny's finite-set heuristics.
    ensures forall cu :: cu in CUsInDisk() <==> ValidCU(cu)
  {
    set au,offset | 0<=au<DiskSizeInAU() && 0<=offset<AUSizeInCUs() :: CU(au,offset)
  }

  type DiskView = map<CU, UninterpretedDiskPage>
}
