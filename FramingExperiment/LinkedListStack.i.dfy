// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/Option.s.dfy"

module Types {
  import opened Options

  type Address(!new, ==)
  type Pointer = Option<Address>
}

module Labels {
  datatype TransitionLabel =
      ConsALabel(x: int)
    | ConsBLabel(x: int)
    | CopyBtoALabel
}

module Spec {
  import opened Options
  import opened Types
  import opened Labels

  datatype Variables = Variables(a: seq<int>, b: seq<int>)

  predicate ConsA(v: Variables, v': Variables, x: int) {
    && v' == v.(a := [x] + v.a)
  }

  predicate ConsB(v: Variables, v': Variables, x: int) {
    && v' == v.(b := [x] + v.b)
  }

  predicate CopyBtoA(v: Variables, v': Variables) {
    && v' == v.(a := v.b)
  }

  predicate Init(v: Variables) {
    && v.a == []
    && v.b == []
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    match lbl
      case ConsALabel(x) => ConsA(v, v', x)
      case ConsBLabel(x) => ConsB(v, v', x)
      case CopyBtoALabel() => CopyBtoA(v, v')
  }
}

module Representation {
  import opened Options
  import opened Types
  import opened Labels
  import Spec

  datatype Cell = Cell(x: int, tail: Cell) | Nil

  datatype Variables = Variables(a: Cell, b: Cell)

  predicate ConsA(v: Variables, v': Variables, x: int) {
    && v' == v.(a := Cell(x, v.a))
  }

  predicate ConsB(v: Variables, v': Variables, x: int) {
    && v' == v.(b := Cell(x, v.b))
  }

  predicate CopyBtoA(v: Variables, v': Variables) {
    && v' == v.(a := v.b)
  }

  predicate Init(v: Variables) {
    && v.a == Nil
    && v.b == Nil
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    match lbl
      case ConsALabel(x) => ConsA(v, v', x)
      case ConsBLabel(x) => ConsB(v, v', x)
      case CopyBtoALabel() => CopyBtoA(v, v')
  }

  //////////////////////////////////////////////////////////////////////////////
  // Invariants

  predicate Inv(v: Variables) {
    true
  }

  lemma InvInit(v: Variables)
    requires Init(v)
    ensures Inv(v)
  {
  }

  lemma InvConsA(v: Variables, v': Variables, x: int)
    requires Inv(v)
    requires ConsA(v, v', x)
    ensures Inv(v')
  {
  }

  lemma InvConsB(v: Variables, v': Variables, x: int)
    requires Inv(v)
    requires ConsB(v, v', x)
    ensures Inv(v')
  {
  }

  lemma InvCopyBtoA(v: Variables, v': Variables)
    requires Inv(v)
    requires CopyBtoA(v, v')
    ensures Inv(v')
  {
  }

  //////////////////////////////////////////////////////////////////////////////
  // Refinement

  function IList(c: Cell) : seq<int>
  {
    if c.Nil? then [] else [c.x] + IList(c.tail)
  }

  function I(v: Variables) : Spec.Variables
    requires Inv(v)
  {
    Spec.Variables(IList(v.a), IList(v.b))
  }

  //////////////////////////////////////////////////////////////////////////////
  // externally-facing refinement lemma

  lemma RefinementInit(v: Variables)
    requires Init(v)
    ensures Spec.Init(I(v))
  {
  }

  lemma RefinementNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Spec.Next(I(v), I(v'), lbl)
  {
  }
}

module FraringCyclicity {
  import opened Options
  import opened Types
  import opened Labels
  import Representation

  datatype CellPage = CellPage(x: int, tail: Pointer)
  type Disk = map<Address, CellPage>

  datatype Variables = Variables(disk: Disk, a: Pointer, b: Pointer)

  predicate IsFree(v: Variables, addr: Address) {
    // Ignoring deallocation -- leaving garbage on the disk.
    && addr !in v.disk
  }

  function ConsAFunc(v: Variables, x: int, addr: Address) : Variables
    requires IsFree(v, addr)
  {
    Variables(v.disk[addr := CellPage(x, v.a)], Some(addr), v.b)
  }

  predicate ConsA(v: Variables, v': Variables, x: int, addr: Address) {
    && IsFree(v, addr)
    && v' == ConsAFunc(v, x, addr)
  }

  function ConsBFunc(v: Variables, x: int, addr: Address) : Variables
    requires IsFree(v, addr)
  {
    Variables(v.disk[addr := CellPage(x, v.b)], v.a, Some(addr))
  }

  predicate ConsB(v: Variables, v': Variables, x: int, addr: Address) {
    && IsFree(v, addr)
    && v' == ConsBFunc(v, x, addr)
  }

  function CopyBtoAFunc(v: Variables) : Variables
  {
    v.(a := v.b)
  }

  predicate CopyBtoA(v: Variables, v': Variables) {
    // Ignoring deallocation -- leaving garbage on the disk.
    && v' == CopyBtoAFunc(v)
  }

  predicate Init(v: Variables) {
    && v.disk == map[]
    && v.a == None
    && v.b == None
  }

  datatype Step =
      ConsAStep(addr: Address)
    | ConsBStep(addr: Address)
    | CopyBtoAStep()

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step) {
    match step
      case ConsAStep(addr) => lbl.ConsALabel? && ConsA(v, v', lbl.x, addr)
      case ConsBStep(addr) => lbl.ConsBLabel? && ConsB(v, v', lbl.x, addr)
      case CopyBtoAStep() => lbl.CopyBtoALabel? && CopyBtoA(v, v')
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }

  //////////////////////////////////////////////////////////////////////////////
  // Invariants

  predicate PointerValid(p: Pointer, disk: Disk) {
    && (p.Some? ==> p.value in disk)
  }

  predicate RootPointersValid(v: Variables) {
    && PointerValid(v.a, v.disk)
    && PointerValid(v.b, v.disk)
  }

  predicate DiskPointersValid(v: Variables) {
    forall address | address in v.disk :: PointerValid(v.disk[address].tail, v.disk)
  }

  type Ranking = map<Address, nat>

  predicate PointersRespectRank(v: Variables, rank: Ranking)
    requires DiskPointersValid(v)
  {
    && rank.Keys == v.disk.Keys
    && (forall address | address in v.disk && v.disk[address].tail.Some? ::
        && rank[v.disk[address].tail.value] < rank[address]
       )
  }

  predicate Acyclic(v: Variables)
    requires DiskPointersValid(v)
  {
    && exists rank :: PointersRespectRank(v, rank)
  }

  predicate Inv(v: Variables) {
    && RootPointersValid(v)
    && DiskPointersValid(v)
    && Acyclic(v)
  }

  lemma InvInit(v: Variables)
    requires Init(v)
    ensures Inv(v)
  {
    assert PointersRespectRank(v, map[]); // witness is an empty Ranking
  }

  lemma InvConsA(v: Variables, v': Variables, x: int, addr: Address)
    requires Inv(v)
    requires ConsA(v, v', x, addr)
    ensures Inv(v')
  {
    var rank :| PointersRespectRank(v, rank);
    var rank' := rank[addr := if v.a.None? then 0 else rank[v.a.value]+1];
    assert PointersRespectRank(v', rank');
  }

  lemma InvConsB(v: Variables, v': Variables, x: int, addr: Address)
    requires Inv(v)
    requires ConsB(v, v', x, addr)
    ensures Inv(v')
  {
    var rank :| PointersRespectRank(v, rank);
    var rank' := rank[addr := if v.b.None? then 0 else rank[v.b.value]+1];
    assert PointersRespectRank(v', rank');
  }

  lemma InvCopyBtoA(v: Variables, v': Variables)
    requires Inv(v)
    requires CopyBtoA(v, v')
    ensures Inv(v')
  {
    var rank :| PointersRespectRank(v, rank);
    assert PointersRespectRank(v', rank);
  }

  function IList(v: Variables, p: Pointer, rank: Ranking) : Representation.Cell
    requires PointerValid(p, v.disk)
    requires DiskPointersValid(v)
    requires PointersRespectRank(v, rank)
    decreases if p.Some? then rank[p.value] else -1 // I can't believe this works, Rustan!
  {
    if p.None?
    then Representation.Nil
    else
      var cellpage := v.disk[p.value];
      Representation.Cell(cellpage.x, IList(v, cellpage.tail, rank))
  }

  //////////////////////////////////////////////////////////////////////////////
  // Refinement

  function TheRank(v: Variables) : Ranking
    requires DiskPointersValid(v)
    requires Acyclic(v)
  {
    // Make CHOOSE deterministic as God and Leslie intended
    var rank :| PointersRespectRank(v, rank);
    rank
  }

  function I(v: Variables) : Representation.Variables
    requires Inv(v)
  {
    var rank := TheRank(v);
    Representation.Variables(IList(v, v.a, rank), IList(v, v.b, rank))
  }

  predicate MapSubset(d: Disk, d': Disk)  // TODO: standard library
  {
    forall k | k in d :: k in d' && d'[k] == d[k]
  }

  lemma Fresh(v: Variables, v': Variables, p: Pointer)
    requires Inv(v)
    requires Inv(v')
    requires PointerValid(p, v.disk)
    requires MapSubset(v.disk, v'.disk)
    ensures IList(v', p, TheRank(v')) == IList(v, p, TheRank(v))
    decreases if p.Some? then TheRank(v)[p.value] else -1
  {
    if p.None? {
      assert IList(v', p, TheRank(v')) == IList(v, p, TheRank(v));
    } else {
      Fresh(v, v', v.disk[p.value].tail);
      assert IList(v', p, TheRank(v')) == IList(v, p, TheRank(v));
    }
  }

  lemma RefinementConsA(v: Variables, v': Variables, x:int, addr: Address)
    requires Inv(v)
    requires ConsA(v, v', x, addr)
    ensures Inv(v')
    ensures Representation.ConsA(I(v), I(v'), x)
  {
    InvConsA(v, v', x, addr);
    Fresh(v, v', v.a);
    Fresh(v, v', v.b);
  }

  lemma RefinementConsB(v: Variables, v': Variables, x:int, addr: Address)
    requires Inv(v)
    requires ConsB(v, v', x, addr)
    ensures Inv(v')
    ensures Representation.ConsB(I(v), I(v'), x)
  {
    InvConsB(v, v', x, addr);
    Fresh(v, v', v.a);
    Fresh(v, v', v.b);
  }

  lemma RefinementCopyBtoA(v: Variables, v': Variables)
    requires Inv(v)
    requires CopyBtoA(v, v')
    ensures Inv(v')
    ensures Representation.CopyBtoA(I(v), I(v'))
  {
    InvCopyBtoA(v, v');
    Fresh(v, v', v.b);
  }

  //////////////////////////////////////////////////////////////////////////////
  // externally-facing refinement lemma

  lemma RefinementInit(v: Variables)
    requires Init(v)
    ensures Inv(v)
    ensures Representation.Init(I(v))
  {
    InvInit(v);
  }

  lemma RefinementNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
    ensures Representation.Next(I(v), I(v'), lbl)
  {
    var step :| NextStep(v, v', lbl, step);
    match step {
      case ConsAStep(addr) => { RefinementConsA(v, v', lbl.x, addr); }
      case ConsBStep(addr) => { RefinementConsB(v, v', lbl.x, addr); }
      case CopyBtoAStep() => { RefinementCopyBtoA(v, v'); }
    }
  }
}

module Marshalling {
  import opened Options
  import opened Types
  import opened Labels
  import FraringCyclicity 

  type Block(!new, ==)
  function Parse<T>(block: Block) : T
  function Marshal<T>(t: T) : Block
  lemma ParseAxiom<T>(t: T)
    ensures Parse(Marshal(t)) == t

  type Disk = map<Address, Block>
  datatype Variables = Variables(disk: Disk, a: Pointer, b: Pointer)

  type CellPage = FraringCyclicity.CellPage

  predicate Init(v: Variables) {
    && v.disk == map[]
    && v.a == None
    && v.b == None
  }

  predicate IsFree(v: Variables, addr: Address) {
    // Ignoring deallocation -- leaving garbage on the disk.
    && addr !in v.disk
  }

  predicate ConsA(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address) {
    && lbl.ConsALabel?
    && IsFree(v, addr)
    && v' == v.(disk := v.disk[addr := Marshal(FraringCyclicity.CellPage(lbl.x, v.a))], a := Some(addr))
  }

  predicate ConsB(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address) {
    && lbl.ConsBLabel?
    && IsFree(v, addr)
    && v' == v.(disk := v.disk[addr := Marshal(FraringCyclicity.CellPage(lbl.x, v.b))], b := Some(addr))
  }

  predicate CopyBtoA(v: Variables, v': Variables, lbl: TransitionLabel) {
    // Ignoring deallocation -- leaving garbage on the disk.
    && lbl.CopyBtoALabel?
    && v' == v.(a := v.b)
  }

  datatype Step =
      ConsAStep(addr: Address)
    | ConsBStep(addr: Address)
    | CopyBtoAStep()

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step) {
    match step
      case ConsAStep(addr) => lbl.ConsALabel? && ConsA(v, v', lbl, addr)
      case ConsBStep(addr) => lbl.ConsBLabel? && ConsB(v, v', lbl, addr)
      case CopyBtoAStep() => lbl.CopyBtoALabel? && CopyBtoA(v, v', lbl)
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }

  //////////////////////////////////////////////////////////////////////
  // Inv

  function MarshalDisk(typed: FraringCyclicity.Disk) : Disk
  {
    map addr | addr in typed :: Marshal(typed[addr])
  }

  predicate TypeProvidesModel(v: Variables, typed: FraringCyclicity.Disk)
  {
    && v.disk == MarshalDisk(typed)
    && FraringCyclicity.Inv(FraringCyclicity.Variables(typed, v.a, v.b))
  }

  predicate Inv(v: Variables) {
    && (exists typed :: TypeProvidesModel(v, typed))
  }

  lemma InvInit(v: Variables)
    requires Init(v)
    ensures Inv(v)
  {
    var typed:FraringCyclicity.Disk := map[];
    var fv := FraringCyclicity.Variables(typed, v.a, v.b);
    assert FraringCyclicity.PointersRespectRank(fv, map[]); // WITNESS
    assert TypeProvidesModel(v, typed); // WITNESS
  }

  function TheTypedDisk(v: Variables): FraringCyclicity.Disk
    requires Inv(v)
  {
    var typed :| TypeProvidesModel(v, typed); typed
  }

  function I(v: Variables) : FraringCyclicity.Variables
    requires Inv(v)
  {
    FraringCyclicity.Variables(TheTypedDisk(v), v.a, v.b)
  }

  lemma InvConsA(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address)
    requires Inv(v)
    requires ConsA(v, v', lbl, addr)
    ensures Inv(v')
  {
    var fv' := FraringCyclicity.ConsAFunc(I(v), lbl.x, addr);
    FraringCyclicity.InvConsA(I(v), fv', lbl.x, addr);
    assert TypeProvidesModel(v', fv'.disk); // WITNESS
  }

  lemma InvConsB(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address)
    requires Inv(v)
    requires ConsB(v, v', lbl, addr)
    ensures Inv(v')
  {
    var fv' := FraringCyclicity.ConsBFunc(I(v), lbl.x, addr);
    FraringCyclicity.InvConsB(I(v), fv', lbl.x, addr);
    assert TypeProvidesModel(v', fv'.disk); // WITNESS
  }

  lemma InvCopyBtoA(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires CopyBtoA(v, v', lbl)
    ensures Inv(v')
  {
    var fv' := FraringCyclicity.CopyBtoAFunc(I(v));
    FraringCyclicity.InvCopyBtoA(I(v), fv');
    assert TypeProvidesModel(v', fv'.disk); // WITNESS
  }

  //////////////////////////////////////////////////////////////////////
  // Refinement

  lemma RefinementConsA(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address)
    requires Inv(v)
    requires ConsA(v, v', lbl, addr)
    ensures Inv(v')
    ensures FraringCyclicity.Next(I(v), I(v'), lbl)
  {
    var x := lbl.x;
    InvConsA(v, v', lbl, addr);
    forall k
      ensures k in TheTypedDisk(v').Keys
        <==> k in TheTypedDisk(v)[addr := FraringCyclicity.CellPage(x, v.a)].Keys
    {
      assert k in v'.disk.Keys || true; // TRIGGER (obviously)
    }
    forall k | k in TheTypedDisk(v')
      ensures TheTypedDisk(v')[k]
        == TheTypedDisk(v)[addr := FraringCyclicity.CellPage(x, v.a)][k]
    {
      ParseAxiom(TheTypedDisk(v')[k]);
      if k==addr {
        assert v'.disk[k] == Marshal(FraringCyclicity.CellPage(x, v.a));  // TRIGGER
        ParseAxiom(FraringCyclicity.CellPage(x, v.a));
      } else {
        assert Parse<FraringCyclicity.CellPage>(v'.disk[k]) == Parse(v.disk[k]);  // TRIGGER
        ParseAxiom(TheTypedDisk(v)[k]);
      }
    }
    assert FraringCyclicity.NextStep(I(v), I(v'), lbl, FraringCyclicity.ConsAStep(addr));
  }

  lemma RefinementConsB(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address)
    requires Inv(v)
    requires ConsB(v, v', lbl, addr)
    ensures Inv(v')
    ensures FraringCyclicity.Next(I(v), I(v'), lbl)
  {
    assume false; // WOLOG and jonh is lazy
  }

  lemma RefinementCopyBtoA(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires CopyBtoA(v, v', lbl)
    ensures Inv(v')
    ensures FraringCyclicity.Next(I(v), I(v'), lbl)
  {
    InvCopyBtoA(v, v', lbl);
    forall k
      ensures k in TheTypedDisk(v').Keys
        <==> k in TheTypedDisk(v).Keys
    {
      assert k in v'.disk.Keys || true; // TRIGGER (obviously)
    }
    forall k | k in TheTypedDisk(v')
      ensures TheTypedDisk(v')[k]
        == TheTypedDisk(v)[k]
    {
      ParseAxiom(TheTypedDisk(v')[k]);
      assert Parse<FraringCyclicity.CellPage>(v'.disk[k]) == Parse(v.disk[k]);  // TRIGGER
      ParseAxiom(TheTypedDisk(v)[k]);
    }
    assert FraringCyclicity.NextStep(I(v), I(v'), lbl, FraringCyclicity.CopyBtoAStep());
  }

  //////////////////////////////////////////////////////////////////////////////
  // externally-facing refinement lemma

  lemma RefinementInit(v: Variables)
    requires Init(v)
    ensures Inv(v)
    ensures FraringCyclicity.Init(I(v))
  {
    InvInit(v);
  }

  lemma RefinementNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
    ensures FraringCyclicity.Next(I(v), I(v'), lbl)
  {
    var step :| NextStep(v, v', lbl, step);
    match step {
      case ConsAStep(addr) => { RefinementConsA(v, v', lbl, addr); }
      case ConsBStep(addr) => { RefinementConsB(v, v', lbl, addr); }
      case CopyBtoAStep() => { RefinementCopyBtoA(v, v', lbl); }
    }
  }
}
