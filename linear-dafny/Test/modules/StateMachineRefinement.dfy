// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module Ifc {
  type TransitionLabel(==,!new)
}

module MapIfc refines Ifc {
  datatype TransitionLabel =
    | Query(k: int, value: int)
    | Insert(k: int, value: int)
}

abstract module StateMachine(ifc: Ifc) {
  type Variables(==,!new)
  predicate Init(s: Variables)
  predicate Next(s: Variables, s': Variables, l: ifc.TransitionLabel)
}

module MapStateMachine refines StateMachine(MapIfc)
{
  type Variables = map<int, int>
  predicate Init(s: Variables)
  {
    s == map[]
  }
  predicate Next(s: Variables, s': Variables, l: ifc.TransitionLabel)
  {
    && (l.Query? ==> l.k in s && l.value == s[l.k] && s' == s)
    && (l.Insert? ==> s' == s[l.k := l.value])
  }
}

abstract module StateMachineRefinement(
    ifc: Ifc,
    L: StateMachine(ifc),
    H: StateMachine(ifc))
{
  function I(s: L.Variables) : H.Variables

  lemma InitRefinement(s: L.Variables)
  requires L.Init(s)
  ensures H.Init(I(s))

  lemma NextRefinement(s: L.Variables, s': L.Variables, l: ifc.TransitionLabel)
  requires L.Next(s, s', l)
  ensures H.Next(I(s), I(s'), l)
}

module ComposeRefinements(
    crIfc: Ifc,
    P: StateMachine(crIfc),
    Q: StateMachine(crIfc),
    R: StateMachine(crIfc),
    Ref1: StateMachineRefinement(crIfc, P, Q),
    Ref2: StateMachineRefinement(crIfc, Q, R)
)
  refines StateMachineRefinement(crIfc, P, R)
{
  function I(s: L.Variables) : H.Variables
  {
    Ref2.I(Ref1.I(s))
  }

  lemma InitRefinement(s: L.Variables)
  {
    Ref1.InitRefinement(s);
    Ref2.InitRefinement(Ref1.I(s));
  }

  lemma NextRefinement(s: L.Variables, s': L.Variables, l: ifc.TransitionLabel)
  {
    Ref1.NextRefinement(s, s', l);
    Ref2.NextRefinement(Ref1.I(s), Ref1.I(s'), l);
  }
}

module MapStateMachine2 refines StateMachine(MapIfc)
{
  datatype Variables = X(m: map<int, int>)
  predicate Init(s: Variables)
  {
    s.m == map[]
  }
  predicate Next(s: Variables, s': Variables, l: ifc.TransitionLabel)
  {
    && (l.Query? ==> l.k in s.m && l.value == s.m[l.k] && s'.m == s.m)
    && (l.Insert? ==> s'.m == s.m[l.k := l.value])
  }
}

module MapStateMachine3 refines StateMachine(MapIfc)
{
  datatype Variables = Y(n: map<int, int>)
  predicate Init(s: Variables)
  {
    s.n == map[]
  }
  predicate Next(s: Variables, s': Variables, l: ifc.TransitionLabel)
  {
    && (l.Query? ==> l.k in s.n && l.value == s.n[l.k] && s'.n == s.n)
    && (l.Insert? ==> s'.n == s.n[l.k := l.value])
  }
}

module Refinement_1_2 refines StateMachineRefinement(MapIfc, MapStateMachine, MapStateMachine2)
{
  function I(s: L.Variables) : H.Variables
  {
    H.X(s)
  }

  lemma InitRefinement(s: L.Variables)
  {
  }

  lemma NextRefinement(s: L.Variables, s': L.Variables, l: ifc.TransitionLabel)
  {
  }
}

module Refinement_2_3 refines StateMachineRefinement(MapIfc, MapStateMachine2, MapStateMachine3)
{
  function I(s: L.Variables) : H.Variables
  {
    H.Y(s.m)
  }

  lemma InitRefinement(s: L.Variables)
  {
  }

  lemma NextRefinement(s: L.Variables, s': L.Variables, l: ifc.TransitionLabel)
  {
  }
}

abstract module Final {
  import BigRef = ComposeRefinements(
      MapIfc,
      MapStateMachine,
      MapStateMachine2,
      MapStateMachine3,
      Refinement_1_2,
      Refinement_2_3)
  import A = MapStateMachine
  import B = MapStateMachine3
  import MapIfc

  lemma stuff() {
    var s : A.Variables := map[];
    var BigRefIs := BigRef.I(s);
    assert BigRef.I(s) // H.Variables = MapStateMachine3.Variables
           ==
           B.Y(map[]); // MapStateMachine3.Variables
    BigRef.InitRefinement(s);

    BigRef.NextRefinement(
        map[1 := 2],
        map[1 := 2],
        MapIfc.Query(1, 2));
  }

  lemma names_for_same_type(
      a: MapIfc.TransitionLabel,
      b: A.ifc.TransitionLabel,
      c: B.ifc.TransitionLabel,
      d: BigRef.ifc.TransitionLabel,
      e: BigRef.P.ifc.TransitionLabel,
      f: BigRef.Q.ifc.TransitionLabel,
      g: BigRef.R.ifc.TransitionLabel,
      h: BigRef.Ref1.L.ifc.TransitionLabel,
      i: BigRef.Ref1.H.ifc.TransitionLabel,
      j: BigRef.Ref2.L.ifc.TransitionLabel,
      k: BigRef.Ref2.H.ifc.TransitionLabel)
  requires a == b == c == d == e == f
      == g == h == i == j == k
  {
  }

}
