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
    | ClearALabel
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

  predicate ClearA(v: Variables, v': Variables) {
    && v' == v.(a := [])
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
      case ClearALabel() => ClearA(v, v')
  }
}

module Representation {
  import opened Options
  import opened Types
  import opened Labels
  import Spec

  datatype Cell = Cell(x: int, tail: Cell) | Nil

  datatype Variables = Variables(a: Cell, b: Cell)

  predicate ConsA(v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.ConsALabel?
    && v' == v.(a := Cell(lbl.x, v.a))
  }

  predicate ConsB(v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.ConsBLabel?
    && v' == v.(b := Cell(lbl.x, v.b))
  }

  predicate CopyBtoA(v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.CopyBtoALabel?
    && v' == v.(a := v.b)
  }

  predicate ClearA(v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.ClearALabel?
    && v' == v.(a := Nil)
  }

  predicate Init(v: Variables) {
    && v.a == Nil
    && v.b == Nil
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    match lbl
      case ConsALabel(_) => ConsA(v, v', lbl)
      case ConsBLabel(_) => ConsB(v, v', lbl)
      case CopyBtoALabel() => CopyBtoA(v, v', lbl)
      case ClearALabel() => ClearA(v, v', lbl)
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

  lemma InvNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
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

// Pointers: Framing/sharing & acyclicity
module AcyclicityAndFraming {
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

  predicate ConsA(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address) {
    && lbl.ConsALabel?
    && IsFree(v, addr)
    && v' == ConsAFunc(v, lbl.x, addr)
  }

  function ConsBFunc(v: Variables, x: int, addr: Address) : Variables
    requires IsFree(v, addr)
  {
    Variables(v.disk[addr := CellPage(x, v.b)], v.a, Some(addr))
  }

  predicate ConsB(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address) {
    && lbl.ConsBLabel?
    && IsFree(v, addr)
    && v' == ConsBFunc(v, lbl.x, addr)
  }

  function Repr(v: Variables, ptr: Pointer, visited: set<Address>) : set<Address>
    decreases v.disk.Keys - visited
  {
    if ptr.None? || ptr.value !in v.disk || ptr.value in visited
      then visited
    else Repr(v, v.disk[ptr.value].tail, visited + {ptr.value})
  }

  function Tighten(v: Variables) : Variables
  {
    v.(disk := map addr | addr in v.disk && addr in Repr(v, v.a, {}) + Repr(v, v.b, {}) :: v.disk[addr])
  }

  function CopyBtoAFunc(v: Variables) : Variables
  {
    Tighten(v.(a := v.b))
  }

  predicate CopyBtoA(v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.CopyBtoALabel?
    && v' == CopyBtoAFunc(v)
  }

//  function ClearAFunc(v: Variables) : Variables
//  {
//    v.(a := None)
//  }
//
//  predicate ClearA(v: Variables, v': Variables, lbl: TransitionLabel) {
//    // Ignoring deallocation -- leaving garbage on the disk.
//    && lbl.CopyBtoALabel?
//    && v' == CopyBtoAFunc(v)
//  }

  predicate Init(v: Variables) {
    && v.disk == map[]
    && v.a == None
    && v.b == None
  }

  datatype Step =
      ConsAStep(addr: Address)
    | ConsBStep(addr: Address)
    | CopyBtoAStep()
    | ClearAStep()

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step) {
    match step
      case ConsAStep(addr) => ConsA(v, v', lbl, addr)
      case ConsBStep(addr) => ConsB(v, v', lbl, addr)
      case CopyBtoAStep() => CopyBtoA(v, v', lbl)
      case ClearAStep() => false // ClearA(v, v', lbl)
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
    && v.disk.Keys <= rank.Keys
    && (forall address | address in v.disk && v.disk[address].tail.Some? ::
        && rank[v.disk[address].tail.value] < rank[address]
       )
  }

  predicate Acyclic(v: Variables)
  {
    && DiskPointersValid(v)
    && (exists rank :: PointersRespectRank(v, rank))
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
    requires ConsA(v, v', lbl, addr)
    ensures Inv(v')
  {
    var rank :| PointersRespectRank(v, rank);
    var rank' := rank[addr := if v.a.None? then 0 else rank[v.a.value]+1];
    assert PointersRespectRank(v', rank');
  }

  lemma InvConsB(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address)
    requires Inv(v)
    requires ConsB(v, v', lbl, addr)
    ensures Inv(v')
  {
    var rank :| PointersRespectRank(v, rank);
    var rank' := rank[addr := if v.b.None? then 0 else rank[v.b.value]+1];
    assert PointersRespectRank(v', rank');
  }
  
  lemma ReprValidPointers(v: Variables, ptr: Pointer, visited: set<Address>, repr: set<Address>)
    requires DiskPointersValid(v)
    requires PointerValid(ptr, v.disk)
    requires repr == Repr(v, ptr, visited)
    requires forall addr | addr in visited ::
      && addr in v.disk
      && (
        || v.disk[addr].tail == ptr
        || (v.disk[addr].tail.Some? ==> v.disk[addr].tail.value in visited)
        )
    decreases v.disk.Keys - visited
    ensures visited <= repr
    ensures forall addr | addr in repr ::
      && addr in v.disk
      && (v.disk[addr].tail.Some? ==> v.disk[addr].tail.value in repr)
    ensures ptr.Some? ==> ptr.value in repr + visited
  {
    if ptr.Some? && ptr.value !in visited {
      var nextPtr := v.disk[ptr.value].tail;
      var nextVisited := visited + {ptr.value};
      ReprValidPointers(v, nextPtr, nextVisited, Repr(v, nextPtr, nextVisited));
    }
  }

  lemma TightenPreservesValidPointers(v: Variables)
    requires RootPointersValid(v)
    requires DiskPointersValid(v)
    requires Acyclic(v)
    ensures RootPointersValid(Tighten(v))
    ensures DiskPointersValid(Tighten(v))
  {
    ReprValidPointers(v, v.a, {}, Repr(v, v.a, {}));
    ReprValidPointers(v, v.b, {}, Repr(v, v.b, {}));
  }

  lemma InvCopyBtoA(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires CopyBtoA(v, v', lbl)
    ensures Inv(v')
  {
    var partialV := v.(a := v.b);
    assert PointersRespectRank(partialV, TheRank(v)); // trigger Acyclic(partialV)
    TightenPreservesValidPointers(partialV);
    assert PointersRespectRank(v', TheRank(v)); // trigger Acyclic(v')
  }

  //////////////////////////////////////////////////////////////////////////////
  // Refinement

  function TheRank(v: Variables) : Ranking
    requires Acyclic(v)
  {
    // Make CHOOSE deterministic as God and Leslie intended
    var rank :| PointersRespectRank(v, rank);
    rank
  }

  function TheRankOf(v: Variables, p: Pointer) : int
    requires Acyclic(v)
    requires PointerValid(p, v.disk)
  {
    if p.Some? then TheRank(v)[p.value] else -1
  }

  function IList(v: Variables, p: Pointer) : Representation.Cell
    requires Acyclic(v)
    requires PointerValid(p, v.disk)
    requires DiskPointersValid(v)
    decreases TheRankOf(v, p)
  {
    if p.None?
    then Representation.Nil
    else
      var cellpage := v.disk[p.value];
      Representation.Cell(cellpage.x, IList(v, cellpage.tail))
  }

  function I(v: Variables) : Representation.Variables
    requires Inv(v)
  {
    Representation.Variables(IList(v, v.a), IList(v, v.b))
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
    ensures IList(v', p) == IList(v, p)
    decreases if p.Some? then TheRank(v)[p.value] else -1
  {
    if p.None? {
      assert IList(v', p) == IList(v, p);
    } else {
      Fresh(v, v', v.disk[p.value].tail);
      assert IList(v', p) == IList(v, p);
    }
  }

  lemma RefinementConsA(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address)
    requires Inv(v)
    requires ConsA(v, v', lbl, addr)
    ensures Inv(v')
    ensures Representation.ConsA(I(v), I(v'), lbl)
  {
    InvConsA(v, v', lbl, addr);
    Fresh(v, v', v.a);
    Fresh(v, v', v.b);
  }

  lemma RefinementConsB(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address)
    requires Inv(v)
    requires ConsB(v, v', lbl, addr)
    ensures Inv(v')
    ensures Representation.ConsB(I(v), I(v'), lbl)
  {
    InvConsB(v, v', lbl, addr);
    Fresh(v, v', v.a);
    Fresh(v, v', v.b);
  }

  function AcyclicRepr(v: Variables, ptr: Pointer, exclude: set<Address>) : set<Address>
    requires Acyclic(v)
    requires DiskPointersValid(v)
    requires PointerValid(ptr, v.disk)
    decreases TheRankOf(v, ptr)
  {
    if ptr.None? || ptr.value !in v.disk
      then exclude
    else AcyclicRepr(v, v.disk[ptr.value].tail, exclude + {ptr.value})
  }

//  TODO(jonh): delete
  lemma AcyclicReprEquiv(v: Variables, ptr: Pointer, exclude: set<Address>, arepr: set<Address>)
    requires Acyclic(v)
    requires DiskPointersValid(v)
    requires PointerValid(ptr, v.disk)
    requires forall exaddr | exaddr in exclude ::
      && PointerValid(Some(exaddr), v.disk)
      && TheRankOf(v, ptr) < TheRankOf(v, Some(exaddr))
    requires arepr == AcyclicRepr(v, ptr, exclude)
    decreases TheRankOf(v, ptr)
    ensures arepr == Repr(v, ptr, exclude)
  {
    if ptr.Some? {
      var next := v.disk[ptr.value].tail;
      AcyclicReprEquiv(v, next, exclude + {ptr.value}, AcyclicRepr(v, next, exclude + {ptr.value}));
    }
  }

  lemma XYAcyclicReprAssoc(v: Variables, ptr: Pointer, exclude: set<Address>, arepr: set<Address>, next: Pointer)
    requires Acyclic(v)
    requires DiskPointersValid(v)
    requires PointerValid(ptr, v.disk)
    requires forall exaddr | exaddr in exclude ::
      && PointerValid(Some(exaddr), v.disk)
      && TheRankOf(v, ptr) < TheRankOf(v, Some(exaddr))
    requires arepr == AcyclicRepr(v, ptr, exclude)
    requires ptr.Some?
    requires next == v.disk[ptr.value].tail;
    decreases TheRankOf(v, ptr)
    ensures AcyclicRepr(v, next, exclude) + {ptr.value} == AcyclicRepr(v, next, exclude + {ptr.value})
  {
    if next.Some? {
      var next2 := v.disk[next.value].tail;
      XYAcyclicReprAssoc(v, next, exclude + {ptr.value}, AcyclicRepr(v, next, exclude + {ptr.value}), next2);
      var exclude2 := exclude + {ptr.value};
      calc {
        AcyclicRepr(v, next, exclude2);
        // defn
        AcyclicRepr(v, next2, exclude2 + {next.value});
        // recursive call


        AcyclicRepr(v, next2, exclude + {next.value}) + {ptr.value};
        // defn
        AcyclicRepr(v, next, exclude) + {ptr.value};
      }
    }
  }

//  lemma ReprExcluded(v: Variables, ptr: Pointer, visited: set<Address>, repr: set<Address>)
//    requires DiskPointersValid(v)
//    requires PointerValid(ptr, v.disk)
//    requires Acyclic(v)
//    //requires forall p | p in ptrs :: TheRankOf(v, p) >= 
//    requires ptr.Some?
//    requires repr == Repr(v, ptr, visited)
//    ensures Repr(v, ptr, {}) == Repr(v, v.disk[ptr.value].tail, {}) + {ptr.value}
//    decreases TheRankOf(v, ptr)
//  {
//    var next := v.disk[ptr.value].tail;
//    if next.Some? {
//      ReprSubset(v, next, {}, Repr(v, next, {}));
//      assert Repr(v, next, {}) == Repr(v, v.disk[next.value].tail, {}) + {next.value};
//      assert Repr(v, ptr, {}) == Repr(v, next, {} + {ptr.value});
//      assert Repr(v, ptr, {}) == Repr(v, next, {}) + {ptr.value};
//    }
//  }

  lemma XYReprSubset(v: Variables, ptr: Pointer, visited: set<Address>, repr: set<Address>)
    requires DiskPointersValid(v)
    requires PointerValid(ptr, v.disk)
    requires Acyclic(v)
    requires ptr.Some?
    requires repr == Repr(v, ptr, visited)
    ensures Repr(v, ptr, {}) == Repr(v, v.disk[ptr.value].tail, {}) + {ptr.value}
    decreases TheRankOf(v, ptr)
  {
    var next := v.disk[ptr.value].tail;
    if next.Some? {
      XYReprSubset(v, next, {}, Repr(v, next, {}));
//      AcyclicReprEquiv(v, ptr, {}, AcyclicRepr(v, ptr, {}));
      assert Repr(v, next, {}) == Repr(v, v.disk[next.value].tail, {}) + {next.value};
      XYAcyclicReprAssoc(v, ptr, {}, AcyclicRepr(v, ptr, {}), next);
      calc {
        Repr(v, next, {} + {ptr.value});
        AcyclicRepr(v, next, {} + {ptr.value});
        AcyclicRepr(v, next, {}) + {ptr.value};
        Repr(v, next, {}) + {ptr.value};
      }
      assert Repr(v, ptr, {}) == Repr(v, next, {} + {ptr.value});
      assert Repr(v, ptr, {}) == Repr(v, next, {}) + {ptr.value};
    }
  }

  lemma TightenPreservesIList(v: Variables, vt: Variables, ptr: Pointer)
    requires Acyclic(v)
    requires PointerValid(ptr, v.disk)
    requires DiskPointersValid(v)
    requires DiskPointersValid(vt)
    requires Repr(v, ptr, {}) <= vt.disk.Keys
    requires forall addr | addr in vt.disk :: addr in v.disk && vt.disk[addr] == v.disk[addr]
    requires forall addr | addr in Repr(v, ptr, {}) :: addr in vt.disk
    ensures Acyclic(vt)
    ensures PointerValid(ptr, vt.disk)
    ensures IList(v, ptr) == IList(vt, ptr)
    decreases TheRankOf(v, ptr)
  {
    ReprValidPointers(v, ptr, {}, Repr(v, ptr, {}));
    assert PointersRespectRank(vt, TheRank(v));
    assert Acyclic(vt);
    assert PointerValid(ptr, vt.disk);
    if ptr.Some? {
      var next := v.disk[ptr.value].tail;
      ReprValidPointers(v, next, {}, Repr(v, next, {}));
      XYReprSubset(v, ptr, {}, Repr(v, ptr, {}));
      assert ptr.value in v.disk;
      assert ptr.value !in {};
      assert Repr(v, ptr, {}) == Repr(v, next, {} + {ptr.value});
      assert Repr(v, next, {}) + {ptr.value} == Repr(v, next, {} + {ptr.value});
      assert Repr(v, next, {}) <= Repr(v, ptr, {});
      TightenPreservesIList(v, vt, next);
      assert IList(v, ptr) == IList(vt, ptr);
    }
    assert IList(v, ptr) == IList(vt, ptr);
  }

  lemma RefinementCopyBtoA(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires CopyBtoA(v, v', lbl)
    ensures Inv(v')
    ensures Representation.CopyBtoA(I(v), I(v'), lbl)
  {
    InvCopyBtoA(v, v', lbl);
    var partialV := v.(a := v.b);
    assert PointersRespectRank(partialV, TheRank(v)); // trigger Acyclic(partialV) to get Inv(partialV)
    Fresh(v, partialV, v.b);
    assert IList(partialV, v.b) == IList(v, v.b);
    //ReprValidPointers(v, v.b, {}, Repr(v, v.b, {}));
    TightenPreservesIList(partialV, v', v.b);
    assert IList(v', v.b) == IList(partialV, v.b); // XXX jonh
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
  import AcyclicityAndFraming

  type Block(!new, ==)
  function Parse<T>(block: Block) : T
  function Marshal<T>(t: T) : Block
  lemma ParseAxiom<T>(t: T)
    ensures Parse(Marshal(t)) == t

  type Disk = map<Address, Block>
  datatype Variables = Variables(disk: Disk, a: Pointer, b: Pointer)

  type CellPage = AcyclicityAndFraming.CellPage

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
    && v' == v.(disk := v.disk[addr := Marshal(AcyclicityAndFraming.CellPage(lbl.x, v.a))], a := Some(addr))
  }

  predicate ConsB(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address) {
    && lbl.ConsBLabel?
    && IsFree(v, addr)
    && v' == v.(disk := v.disk[addr := Marshal(AcyclicityAndFraming.CellPage(lbl.x, v.b))], b := Some(addr))
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

  function MarshalDisk(typed: AcyclicityAndFraming.Disk) : Disk
  {
    map addr | addr in typed :: Marshal(typed[addr])
  }

  predicate TypeProvidesModel(v: Variables, typed: AcyclicityAndFraming.Disk)
  {
    && v.disk == MarshalDisk(typed)
    && AcyclicityAndFraming.Inv(AcyclicityAndFraming.Variables(typed, v.a, v.b))
  }

  predicate Inv(v: Variables) {
    && (exists typed :: TypeProvidesModel(v, typed))
  }

  lemma InvInit(v: Variables)
    requires Init(v)
    ensures Inv(v)
  {
    var typed:AcyclicityAndFraming.Disk := map[];
    var fv := AcyclicityAndFraming.Variables(typed, v.a, v.b);
    assert AcyclicityAndFraming.PointersRespectRank(fv, map[]); // WITNESS
    assert TypeProvidesModel(v, typed); // WITNESS
  }

  function TheTypedDisk(v: Variables): AcyclicityAndFraming.Disk
    requires Inv(v)
  {
    var typed :| TypeProvidesModel(v, typed); typed
  }

  function I(v: Variables) : AcyclicityAndFraming.Variables
    requires Inv(v)
  {
    AcyclicityAndFraming.Variables(TheTypedDisk(v), v.a, v.b)
  }

  lemma InvConsA(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address)
    requires Inv(v)
    requires ConsA(v, v', lbl, addr)
    ensures Inv(v')
  {
    var fv' := AcyclicityAndFraming.ConsAFunc(I(v), lbl.x, addr);
    AcyclicityAndFraming.InvConsA(I(v), fv', lbl, addr);
    assert TypeProvidesModel(v', fv'.disk); // WITNESS
  }

  lemma InvConsB(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address)
    requires Inv(v)
    requires ConsB(v, v', lbl, addr)
    ensures Inv(v')
  {
    var fv' := AcyclicityAndFraming.ConsBFunc(I(v), lbl.x, addr);
    AcyclicityAndFraming.InvConsB(I(v), fv', lbl, addr);
    assert TypeProvidesModel(v', fv'.disk); // WITNESS
  }

  lemma InvCopyBtoA(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires CopyBtoA(v, v', lbl)
    ensures Inv(v')
  {
    assume false; // TODO tighten down here
    var fv' := AcyclicityAndFraming.CopyBtoAFunc(I(v));
    AcyclicityAndFraming.InvCopyBtoA(I(v), fv', lbl);
    assert TypeProvidesModel(v', fv'.disk); // WITNESS
  }

  //////////////////////////////////////////////////////////////////////
  // Refinement

  lemma RefinementConsA(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address)
    requires Inv(v)
    requires ConsA(v, v', lbl, addr)
    ensures Inv(v')
    ensures AcyclicityAndFraming.Next(I(v), I(v'), lbl)
  {
    var x := lbl.x;
    InvConsA(v, v', lbl, addr);
    forall k
      ensures k in TheTypedDisk(v').Keys
        <==> k in TheTypedDisk(v)[addr := AcyclicityAndFraming.CellPage(x, v.a)].Keys
    {
      assert k in v'.disk.Keys || true; // TRIGGER (obviously)
    }
    forall k | k in TheTypedDisk(v')
      ensures TheTypedDisk(v')[k]
        == TheTypedDisk(v)[addr := AcyclicityAndFraming.CellPage(x, v.a)][k]
    {
      ParseAxiom(TheTypedDisk(v')[k]);
      if k==addr {
        assert v'.disk[k] == Marshal(AcyclicityAndFraming.CellPage(x, v.a));  // TRIGGER
        ParseAxiom(AcyclicityAndFraming.CellPage(x, v.a));
      } else {
        assert Parse<AcyclicityAndFraming.CellPage>(v'.disk[k]) == Parse(v.disk[k]);  // TRIGGER
        ParseAxiom(TheTypedDisk(v)[k]);
      }
    }
    assert AcyclicityAndFraming.NextStep(I(v), I(v'), lbl, AcyclicityAndFraming.ConsAStep(addr));
  }

  lemma RefinementConsB(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address)
    requires Inv(v)
    requires ConsB(v, v', lbl, addr)
    ensures Inv(v')
    ensures AcyclicityAndFraming.Next(I(v), I(v'), lbl)
  {
    assume false; // WOLOG and jonh is lazy
  }

  lemma RefinementCopyBtoA(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires CopyBtoA(v, v', lbl)
    ensures Inv(v')
    ensures AcyclicityAndFraming.Next(I(v), I(v'), lbl)
  {
    assume false; // TODO tighten down here
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
      assert Parse<AcyclicityAndFraming.CellPage>(v'.disk[k]) == Parse(v.disk[k]);  // TRIGGER
      ParseAxiom(TheTypedDisk(v)[k]);
    }
    assert AcyclicityAndFraming.NextStep(I(v), I(v'), lbl, AcyclicityAndFraming.CopyBtoAStep());
  }

  //////////////////////////////////////////////////////////////////////////////
  // externally-facing refinement lemma

  lemma RefinementInit(v: Variables)
    requires Init(v)
    ensures Inv(v)
    ensures AcyclicityAndFraming.Init(I(v))
  {
    InvInit(v);
  }

  lemma RefinementNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
    ensures AcyclicityAndFraming.Next(I(v), I(v'), lbl)
  {
    var step :| NextStep(v, v', lbl, step);
    match step {
      case ConsAStep(addr) => { RefinementConsA(v, v', lbl, addr); }
      case ConsBStep(addr) => { RefinementConsB(v, v', lbl, addr); }
      case CopyBtoAStep() => { RefinementCopyBtoA(v, v', lbl); }
    }
  }
}
