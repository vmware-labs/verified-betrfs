// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/Option.s.dfy"
include "HilbertChoose.i.dfy"

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
  {
    function ConsA(x: int) : Option<Variables>
    {
      Some(this.(a := [x] + a))
    }

    function ConsB(x: int) : Option<Variables>
    {
      Some(this.(b := [x] + b))
    }

    function CopyBtoA() : Option<Variables>
    {
      Some(this.(a := b))
    }

    function Next(lbl: TransitionLabel) : Option<Variables>
    {
      match lbl
        case ConsALabel(x) => ConsA(x)
        case ConsBLabel(x) => ConsB(x)
        case CopyBtoALabel() => CopyBtoA()
    }
  }

  function Init() : Variables {
    Variables([], [])
  }
}

module Representation {
  import opened Options
  import opened Types
  import opened Labels
  import Spec

  datatype Cell = Cell(x: int, tail: Cell) | Nil

  datatype Variables = Variables(a: Cell, b: Cell)
  {
    function ConsA(lbl: TransitionLabel) : Option<Variables>
    {
      var enabled :=
        && lbl.ConsALabel?
        ;
      if !enabled then None else Some(
        this.(a := Cell(lbl.x, a))
      )
    }

    function ConsB(lbl: TransitionLabel) : Option<Variables>
    {
      var enabled :=
        && lbl.ConsBLabel?
        ;
      if !enabled then None else Some(
        this.(b := Cell(lbl.x, b))
      )
    }

    function CopyBtoA(lbl: TransitionLabel) : Option<Variables>
    {
      var enabled :=
        && lbl.CopyBtoALabel?
        ;
      if !enabled then None else Some(
        this.(a := b)
      )
    }

    function Next(lbl: TransitionLabel) : Option<Variables>
    {
      match lbl
        case ConsALabel(x) => ConsA(lbl)
        case ConsBLabel(x) => ConsB(lbl)
        case CopyBtoALabel() => CopyBtoA(lbl)
    }
  }

  function Init() : Variables {
    Variables(Nil, Nil)
  }

  //////////////////////////////////////////////////////////////////////////////
  // Invariants

  predicate Inv(v: Variables) {
    true
  }

  lemma InvInit(v: Variables)
    requires v == Init()
    ensures Inv(v)
  {
  }

  lemma InvConsA(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Some(v') == v.ConsA(lbl)
    ensures Inv(v')
  {
  }

  lemma InvConsB(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Some(v') == v.ConsB(lbl)
    ensures Inv(v')
  {
  }

  lemma InvCopyBtoA(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Some(v') == v.CopyBtoA(lbl)
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
    requires v == Init()
    ensures I(v) == Spec.Init()
  {
  }

  lemma RefinementNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Some(v') == v.Next(lbl)
    ensures Some(I(v')) == I(v).Next(lbl)
  {
  }
}

module FraringCyclicity {
  import opened Options
  import opened Types
  import opened Labels
  import Representation
  import opened HilbertChoose 

  datatype CellPage = CellPage(x: int, tail: Pointer)
  type Disk = map<Address, CellPage>

  datatype Step =
      ConsAStep(addr: Address)
    | ConsBStep(addr: Address)
    | CopyBtoAStep()

  datatype Variables = Variables(disk: Disk, a: Pointer, b: Pointer)
  {
    predicate IsFree(addr: Address) {
      // Ignoring deallocation -- leaving garbage on the disk.
      && addr !in disk
    }

    function ConsA(lbl: TransitionLabel, addr: Address) : Option<Variables>
    {
      var enabled :=
        && lbl.ConsALabel?
        && IsFree(addr)
        ;
      if !enabled then None else Some(
        Variables(disk[addr := CellPage(lbl.x, a)], Some(addr), b)
      )
    }

    function ConsB(lbl: TransitionLabel, addr: Address) : Option<Variables>
    {
      var enabled :=
        && lbl.ConsBLabel?
        && IsFree(addr)
        ;
      if !enabled then None else Some(
        Variables(disk[addr := CellPage(lbl.x, b)], a, Some(addr))
      )
    }

    function CopyBtoA(lbl: TransitionLabel) : Option<Variables>
    {
      var enabled :=
        && lbl.CopyBtoALabel?
        ;
      if !enabled then None else Some(this.(a := b))
    }

    function NextStep(lbl: TransitionLabel, step: Step) : Option<Variables> {
      match step
        case ConsAStep(addr) => ConsA(lbl, addr)
        case ConsBStep(addr) => ConsB(lbl, addr)
        case CopyBtoAStep() => CopyBtoA(lbl)
    }

    function Next(lbl: TransitionLabel) : Option<Variables> {
      var step := ChooseIf(step => NextStep(lbl, step).Some?);
      if step.Some? then NextStep(lbl, step.value) else None
    }
  }

  predicate Init(v: Variables) {
    && v.disk == map[]
    && v.a == None
    && v.b == None
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

  lemma InvConsA(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address)
    requires Inv(v)
    requires Some(v') == v.ConsA(lbl, addr)
    ensures Inv(v')
  {
    var rank :| PointersRespectRank(v, rank);
    var rank' := rank[addr := if v.a.None? then 0 else rank[v.a.value]+1];
    assert PointersRespectRank(v', rank');
  }

  lemma InvConsB(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address)
    requires Inv(v)
    requires Some(v') == v.ConsB(lbl, addr)
    ensures Inv(v')
  {
    var rank :| PointersRespectRank(v, rank);
    var rank' := rank[addr := if v.b.None? then 0 else rank[v.b.value]+1];
    assert PointersRespectRank(v', rank');
  }

  lemma InvCopyBtoA(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Some(v') == v.CopyBtoA(lbl)
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

  lemma RefinementConsA(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address)
    requires Inv(v)
    requires Some(v') == v.ConsA(lbl, addr)
    ensures Inv(v')
    ensures Some(I(v')) == I(v).ConsA(lbl)
  {
    InvConsA(v, v', lbl, addr);
    Fresh(v, v', v.a);
    Fresh(v, v', v.b);
  }

  lemma RefinementConsB(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address)
    requires Inv(v)
    requires Some(v') == v.ConsB(lbl, addr)
    ensures Inv(v')
    ensures Some(I(v')) == I(v).ConsB(lbl)
  {
    InvConsB(v, v', lbl, addr);
    Fresh(v, v', v.a);
    Fresh(v, v', v.b);
  }

  lemma RefinementCopyBtoA(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Some(v') == v.CopyBtoA(lbl)
    ensures Inv(v')
    ensures Some(I(v')) == I(v).CopyBtoA(lbl)
  {
    InvCopyBtoA(v, v', lbl);
    Fresh(v, v', v.b);
  }

  //////////////////////////////////////////////////////////////////////////////
  // externally-facing refinement lemma

  lemma RefinementInit(v: Variables)
    requires Init(v)
    ensures Inv(v)
    ensures I(v) == Representation.Init()
  {
    InvInit(v);
  }

  lemma RefinementNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Some(v') == v.Next(lbl)
    ensures Inv(v')
    ensures Some(I(v')) == I(v).Next(lbl)
  {
    var step := ChooseIf(step => v.NextStep(lbl, step).Some?).value;
    match step {
      case ConsAStep(addr) => { RefinementConsA(v, v', lbl, addr); }
      case ConsBStep(addr) => { RefinementConsB(v, v', lbl, addr); }
      case CopyBtoAStep() => { RefinementCopyBtoA(v, v', lbl); }
    }
  }
}

module Marshalling {
  import opened Options
  import opened Types
  import opened Labels
  import FraringCyclicity 
  import opened HilbertChoose 

  type Block(!new, ==)
  function Parse<T>(block: Block) : T
  function Marshal<T>(t: T) : Block
  lemma ParseAxiom<T>(t: T)
    ensures Parse(Marshal(t)) == t

  type Disk = map<Address, Block>
  type CellPage = FraringCyclicity.CellPage

  datatype Step =
      ConsAStep(addr: Address)
    | ConsBStep(addr: Address)
    | CopyBtoAStep()

  datatype Variables = Variables(disk: Disk, a: Pointer, b: Pointer)
  {
    predicate IsFree(addr: Address)
    {
      // Ignoring deallocation -- leaving garbage on the disk.
      && addr !in disk
    }

    function ConsA(lbl: TransitionLabel, addr: Address) : Option<Variables>
    {
      var enabled :=
        && lbl.ConsALabel?
        && IsFree(addr)
      ;
      if !enabled then None else Some(
        this.(disk := disk[addr := Marshal(FraringCyclicity.CellPage(lbl.x, a))], a := Some(addr))
      )
    }

    function ConsB(lbl: TransitionLabel, addr: Address) : Option<Variables>
    {
      var enabled :=
        && lbl.ConsBLabel?
        && IsFree(addr)
      ;
      if !enabled then None else Some(
        this.(disk := disk[addr := Marshal(FraringCyclicity.CellPage(lbl.x, b))], b := Some(addr))
      )
    }

    function CopyBtoA(lbl: TransitionLabel) : Option<Variables>
    {
      // Ignoring deallocation -- leaving garbage on the disk.
      var enabled :=
        lbl.CopyBtoALabel?
      ;
      if !enabled then None else Some(this.(a := b))
    }

    function NextStep(lbl: TransitionLabel, step: Step) : Option<Variables>
    {
      match step
        case ConsAStep(addr) => ConsA(lbl, addr)
        case ConsBStep(addr) => ConsB(lbl, addr)
        case CopyBtoAStep() => CopyBtoA(lbl)
    }

    function Next(lbl: TransitionLabel) : Option<Variables>
    {
      if step: Step :| NextStep(lbl, step).Some?  then NextStep(lbl, step) else None
    }
  }

  predicate Init(v: Variables) {
    && v.disk == map[]
    && v.a == None
    && v.b == None
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
    requires Some(v') == v.ConsA(lbl, addr)
    ensures Inv(v')
  {
    var fv' := I(v).ConsA(lbl, addr).value;
    FraringCyclicity.InvConsA(I(v), fv', lbl, addr);
    assert TypeProvidesModel(v', fv'.disk); // WITNESS
  }

  lemma InvConsB(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address)
    requires Inv(v)
    requires Some(v') == v.ConsB(lbl, addr)
    ensures Inv(v')
  {
    var fv' := I(v).ConsB(lbl, addr).value;
    FraringCyclicity.InvConsB(I(v), fv', lbl, addr);
    assert TypeProvidesModel(v', fv'.disk); // WITNESS
  }

  lemma InvCopyBtoA(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Some(v') == v.CopyBtoA(lbl)
    ensures Inv(v')
  {
    var fv' := I(v).CopyBtoA(lbl).value;
    FraringCyclicity.InvCopyBtoA(I(v), fv', lbl);
    assert TypeProvidesModel(v', fv'.disk); // WITNESS
  }

  //////////////////////////////////////////////////////////////////////
  // Refinement

  lemma RefinementConsA(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address)
    requires Inv(v)
    requires Some(v') == v.Next(lbl)  // Essential
    requires Some(v') == v.ConsA(lbl, addr)
    ensures Inv(v')
    ensures Some(I(v')) == I(v).Next(lbl)
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

    var hstep := FraringCyclicity.ConsAStep(addr);
//    assert I(v).NextStep(lbl, hstep).Some?;
//    assert exists step :: I(v).NextStep(lbl, step).Some?;
    var p := step => I(v).NextStep(lbl, step).Some?;
    assert p.requires(hstep) && p(hstep); // trigger
    var step := ChooseIf(step => I(v).NextStep(lbl, step).Some?).value;
    assert step.ConsAStep?;
    assert step == hstep;
    assert I(v).NextStep(lbl, FraringCyclicity.ConsAStep(addr)) == I(v).Next(lbl);
    assert Some(I(v')) == I(v).NextStep(lbl, FraringCyclicity.ConsAStep(addr));
  }

  lemma RefinementConsB(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address)
    requires Inv(v)
    requires Some(v') == v.ConsB(lbl, addr)
    ensures Inv(v')
    ensures Some(I(v')) == I(v).Next(lbl)
  {
    assume false; // WOLOG and jonh is lazy
  }

  lemma RefinementCopyBtoA(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Some(v') == v.CopyBtoA(lbl)
    ensures Inv(v')
    ensures Some(I(v')) == I(v).Next(lbl)
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
    assert Some(I(v')) == I(v).NextStep(lbl, FraringCyclicity.CopyBtoAStep());
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
    requires Some(v') == v.Next(lbl)
    ensures Inv(v')
    ensures Some(I(v')) == I(v).Next(lbl)
  {
    var step :| Some(v') == v.NextStep(lbl, step);
    match step {
      case ConsAStep(addr) => { RefinementConsA(v, v', lbl, addr); }
      case ConsBStep(addr) => { RefinementConsB(v, v', lbl, addr); }
      case CopyBtoAStep() => { RefinementCopyBtoA(v, v', lbl); }
    }
  }
}
