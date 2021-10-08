// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause


module {:extern "LinearRegion"} LinearRegion {
  type {:extern "predefined"} Region
}


module {:extern "LinearRegionId_s"} LinearRegionId {
  type {:extern "predefined"} RegionId
}

module {:extern "LinearRegionRefCell_s"} LinearRegionRefCell {
  type {:extern "predefined"} RefCell(==)<A>
}

module {:extern "LinearRegionLoc_s"} LinearRegionLoc {
  type {:extern "predefined"} Loc
}



module {:extern "LinearRegion_s"} LinearRegion_s {
  import LinearRegion
  import LinearRegionId
  import LinearRegionRefCell
  import LinearRegionLoc

  type Region = LinearRegion.Region
  type RegionId = LinearRegionId.RegionId
  type RefCell(==)<A> = LinearRegionRefCell.RefCell<A>
  type Loc = LinearRegionLoc.Loc

  // Regions with ML-style ref cells


  function {:axiom} Id(g: Region): RegionId
  function {:axiom} Allocated(g: Region): set<Loc>
  function {:axiom} RefLoc<A>(r: RefCell<A>): Loc
  function {:axiom} LocRef<A(00)>(l: Loc): RefCell<A>

  predicate {:axiom} ValidRef(loc: Loc, id: RegionId, is_linear: bool)

  function {:axiom} Get<A>(g: Region, r: RefCell<A>): A

  function {:axiom} Modifies(locs: set<Loc>, g1: Region, g2: Region): (b: bool)
    ensures b ==> Id(g1) == Id(g2)
    ensures b ==> Allocated(g1) <= Allocated(g2)

  function method {:extern "LinearRegion_s", "Read"} Read<A>(shared g: Region, r: RefCell<A>): (a: A)
    requires ValidRef(RefLoc(r), Id(g), false)
    ensures Get(g, r) == a

  function method {:extern "LinearRegion_s", "Borrow"} Borrow<A>(shared g: Region, r: RefCell<A>): (shared a: A)
    requires ValidRef(RefLoc(r), Id(g), true)
    ensures Get(g, r) == a

  method {:extern "LinearRegion_s", "Write"} Write<A>(linear inout g: Region, r: RefCell<A>, a: A)
    requires ValidRef(RefLoc(r), Id(old_g), false)
    ensures Get(g, r) == a
    ensures Modifies({RefLoc(r)}, old_g, g)

  method {:extern "LinearRegion_s", "Swap"} Swap<A>(linear inout g: Region, r: RefCell<A>, linear inout a: A)
    requires ValidRef(RefLoc(r), Id(old_g), true)
    ensures Get(old_g, r) == a
    ensures Get(g, r) == old_a
    ensures Modifies({RefLoc(r)}, old_g, g)

  method {:extern "LinearRegion_s", "Alloc"} Alloc<A>(linear inout g: Region, a: A) returns(r: RefCell<A>)
    ensures ValidRef(RefLoc(r), Id(g), false)
    ensures Get(g, r) == a
    ensures Modifies({}, old_g, g)
    ensures RefLoc(r) !in Allocated(old_g)
    ensures RefLoc(r) in Allocated(g)

  // TODO: add destructor
  method {:extern "LinearRegion_s", "AllocLinear"} AllocLinear<A>(linear inout g: Region, linear a: A) returns(r: RefCell<A>)
    ensures ValidRef(RefLoc(r), Id(g), true)
    ensures Get(g, r) == a
    ensures Modifies({}, old_g, g)
    ensures RefLoc(r) !in Allocated(old_g)
    ensures RefLoc(r) in Allocated(g)

  method {:extern "LinearRegion_s", "NewRegion"} NewRegion() returns(linear g: Region)

  // Note: freeing the region eliminates the permission to alloc/read/write/swap,
  // but it doesn't immediately free the objects in the region,
  // so if the implementation uses reference counting, you still need to break cycles manually
  method {:extern "LinearRegion_s", "FreeRegion"} FreeRegion(linear g: Region)

  lemma {:axiom} LemmaModifies()
    ensures forall g :: Modifies({}, g, g)
    ensures forall locs1, locs2, g1, g2 ::
      Modifies(locs1, g1, g2) && locs1 <= locs2 ==>
      Modifies(locs2, g1, g2)
    ensures
      forall locs1, locs2, locs3, g1, g2, g3 ::
        Modifies(locs1, g1, g2) && Modifies(locs2, g2, g3) && locs3 == locs1 + locs2 ==>
        Modifies(locs3, g1, g3)

  lemma {:axiom} LemmaUnmodified<A(00)>()
    ensures forall r:RefCell<A> {:trigger RefLoc(r)} :: LocRef(RefLoc(r)) == r
    ensures forall l:Loc {:trigger RefLoc<A>(LocRef(l))} :: RefLoc<A>(LocRef(l)) == l
    ensures
      forall r:RefCell<A>, locs, g1, g2 ::
        Modifies(locs, g1, g2) && RefLoc(r) !in locs ==>
        Get(g1, r) == Get(g2, r)

} // module

module Test_LinearRegion_s {
  import opened LinearRegion_s
  datatype Node = Nil | Cons(data: bool, next: RefCell<Node>, prev: RefCell<Node>)
  method Main()
  {
    linear var g := NewRegion();
    var sentinel := Alloc(inout g, Nil);
    Write(inout g, sentinel, Cons(true, sentinel, sentinel)); // create cycle
    var x := Read(g, sentinel);
    assert x.next == sentinel;
    assert x.prev == sentinel;
    Write(inout g, sentinel, Nil); // break cycle before freeing region to prevent leak
    FreeRegion(g);
  }
}
