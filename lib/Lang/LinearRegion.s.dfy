// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause


module {:extern "LinearRegion_s"} LinearRegion_s {

  // Regions with ML-style ref cells

  type Region
  type RegionId
  type RefCell(==)<A>
  type Loc

  function Id(g: Region): RegionId
  function Allocated(g: Region): set<Loc>
  function RefLoc<A>(r: RefCell<A>): Loc
  function LocRef<A>(l: Loc): RefCell<A>

  predicate ValidRef(loc: Loc, id: RegionId, is_linear: bool)

  function Get<A>(g: Region, r: RefCell<A>): A

  function Modifies(locs: set<Loc>, g1: Region, g2: Region): (b: bool)
    ensures b ==> Id(g1) == Id(g2)
    ensures b ==> Allocated(g1) <= Allocated(g2)

  function method Read<A>(shared g: Region, r: RefCell<A>): (a: A)
    requires ValidRef(RefLoc(r), Id(g), false)
    ensures Get(g, r) == a

  function method Borrow<A>(shared g: Region, r: RefCell<A>): (shared a: A)
    requires ValidRef(RefLoc(r), Id(g), true)
    ensures Get(g, r) == a

  method Write<A>(linear inout g: Region, r: RefCell<A>, a: A)
    requires ValidRef(RefLoc(r), Id(old_g), false)
    ensures Get(g, r) == a
    ensures Modifies({RefLoc(r)}, old_g, g)

  method Swap<A>(linear inout g: Region, r: RefCell<A>, linear inout a: A)
    requires ValidRef(RefLoc(r), Id(old_g), true)
    ensures Get(old_g, r) == a
    ensures Get(g, r) == old_a
    ensures Modifies({RefLoc(r)}, old_g, g)

  method Alloc<A>(linear inout g: Region, a: A) returns(r: RefCell<A>)
    ensures ValidRef(RefLoc(r), Id(g), false)
    ensures Get(g, r) == a
    ensures Modifies({}, old_g, g)
    ensures RefLoc(r) !in Allocated(old_g)
    ensures RefLoc(r) in Allocated(g)

  // TODO: add destructor
  method AllocLinear<A>(linear inout g: Region, linear a: A) returns(r: RefCell<A>)
    ensures ValidRef(RefLoc(r), Id(g), true)
    ensures Get(g, r) == a
    ensures Modifies({}, old_g, g)
    ensures RefLoc(r) !in Allocated(old_g)
    ensures RefLoc(r) in Allocated(g)

  method NewRegion() returns(linear g: Region)

  // Note: freeing the region eliminates the permission to alloc/read/write/swap,
  // but it doesn't immediately free the objects in the region,
  // so if the implementation uses reference counting, you still need to break cycles manually
  method FreeRegion(linear g: Region)

  lemma LemmaModifies()
    ensures forall g :: Modifies({}, g, g)
    ensures forall locs1, locs2, g1, g2 ::
      Modifies(locs1, g1, g2) && locs1 <= locs2 ==>
      Modifies(locs2, g1, g2)
    ensures
      forall locs1, locs2, locs3, g1, g2, g3 ::
        Modifies(locs1, g1, g2) && Modifies(locs2, g2, g3) && locs3 == locs1 + locs2 ==>
        Modifies(locs3, g1, g3)

  lemma LemmaUnmodified<A>()
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
  method M()
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
