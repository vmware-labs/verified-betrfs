include "../lib/NativeTypes.s.dfy"
include "../lib/MutableMap.i.dfy"
include "../lib/Option.s.dfy"

module GraphSpec {
  import opened NativeTypes

  type Reference = uint64

  datatype Constants = Constants
  datatype Variables = Variables(graph: map<Reference, set<Reference>>)

  function method Root(): Reference { 0 }

  predicate Inv(k: Constants, s: Variables)
  {
    && Root() in s.graph
    && forall r | r in s.graph :: forall p | p in s.graph[r] :: p in s.graph
  }

  predicate Init(k: Constants, s': Variables)
  {
    && s' == Variables(map[Root() := {}])
  }

  predicate Alloc(k: Constants, s: Variables, s': Variables, ref: Reference)
  {
    && ref !in s.graph
    && ref as nat < 0x1_0000_0000_0000_0000

    && s' == s.(graph := s.graph[ref := {}])
  }

  predicate Dealloc(k: Constants, s: Variables, s': Variables, ref: Reference)
  {
    && ref in s.graph
    && forall r | r in s.graph :: ref !in s.graph[r]

    && s' == s.(graph := map r | r in s.graph && r != ref :: r := s.graph[r])
  }

  predicate Attach(k: Constants, s: Variables, s': Variables, parent: Reference, ref: Reference)
  {
    && parent in s.graph
    && ref in s.graph
    && ref !in s.graph[parent]

    && s' == s.(graph := s.graph[parent := (s.graph[parent] + {ref})])
  }

  predicate Detach(k: Constants, s: Variables, s': Variables, parent: Reference, ref: Reference)
  {
    && parent in s.graph
    && ref in s.graph
    && ref in s.graph[parent]

    && s' == s.(graph := s.graph[parent := (s.graph[parent] - {ref})])
  }

  datatype Step =
    | AllocStep(ref: Reference) 
    | DeallocStep(ref: Reference)
    | AttachStep(parent: Reference, ref: Reference)
    | DetachStep(parent: Reference, ref: Reference)

  predicate NextStep(k: Constants, s: Variables, s': Variables, step: Step)
  {
    match step {
      case AllocStep(ref) => Alloc(k, s, s', ref)
      case DeallocStep(ref) => Dealloc(k, s, s', ref)
      case AttachStep(parent, ref) => Attach(k, s, s', parent, ref)
      case DetachStep(parent, ref) => Detach(k, s, s', parent, ref)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables)
  {
    exists step: Step :: NextStep(k, s, s', step)
  }
}

module FunctionalGraph /* refines GraphSpec */ {
  import opened NativeTypes
  import S = GraphSpec

  type Reference = S.Reference

  datatype Constants = Constants

  datatype GraphValue = GraphValue(adjList: set<Reference>, rc: uint64)
  datatype Variables = Variables(
      graph: map<Reference, GraphValue>,
      invRc: map<uint64, set<Reference>>,
      nextRef: Reference)

  function Ik(k: Constants): S.Constants
  {
    S.Constants()
  }

  function I(k: Constants, s: Variables): S.Variables
  {
    S.Variables(map k | k in s.graph :: k := s.graph[k].adjList)
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && S.Inv(Ik(k), I(k, s))

    && (forall ref | ref in s.graph :: ref !in s.graph[ref].adjList)

    && (forall r | r in s.graph :: (
      && var c := s.graph[r].rc;
      && c in s.invRc
      && r in s.invRc[c]))
    && (forall c | c in s.invRc :: forall r | r in s.invRc[c] :: r in s.graph)
    && (forall c | c in s.invRc :: forall r | r in s.invRc[c] :: s.graph[r].rc == c)

    && (forall ref | ref in s.graph :: (exists r | r in s.graph :: ref in s.graph[r].adjList) ==> s.graph[ref].rc > 0)
  }

  function Init(k: Constants): (s': Variables)
  {
    Variables(map[S.Root() := GraphValue({}, 0)], map[], 1)
  }

  predicate AllocRequires(k: Constants, s: Variables)
  {
    && s.nextRef as nat < 0x1_0000_0000_0000_0000 - 1
  }

  datatype AllocResult = AllocResult(s': Variables, ref: Reference)
  function Alloc(k: Constants, s: Variables): (result: AllocResult)
  requires Inv(k, s)
  requires AllocRequires(k, s)
  // ensures S.Alloc(Ik(k), I(k, s), I(k, result.s'), result.ref)
  {
    AllocResult(
      s
        .(graph := s.graph[s.nextRef := GraphValue({}, 0)])
        .(invRc := s.invRc[0 := (if 0 in s.invRc then s.invRc[0] else {}) + {s.nextRef}])
        .(nextRef := s.nextRef + 1),
      s.nextRef)
  }

  lemma RefinesAlloc(k: Constants, s: Variables, s': Variables) returns (ref: Reference)
  requires Inv(k, s)
  requires AllocRequires(k, s)
  requires s' == Alloc(k, s).s'
  ensures ref == Alloc(k, s).ref
  ensures Inv(k, s')
  ensures S.Alloc(Ik(k), I(k, s), I(k, s'), ref)
  {
    ref := Alloc(k, s).ref;
    assume S.Inv(Ik(k), I(k, s'));
    assume (forall r | r in s'.graph :: (
      && var c := s'.graph[r].rc;
      && c in s'.invRc
      && r in s'.invRc[c]));
    assume forall c | c in s'.invRc :: forall r | r in s'.invRc[c] :: r in s'.graph;
    assume forall c | c in s'.invRc :: forall r | r in s'.invRc[c] :: s'.graph[r].rc == c;
    assume forall ref | ref in s'.graph :: (exists r | r in s'.graph :: ref in s'.graph[r].adjList) ==> s'.graph[ref].rc > 0;
    assert Inv(k, s');
    assume ref !in s.graph;
    assert S.Alloc(Ik(k), I(k, s), I(k, s'), Alloc(k, s).ref);
  }

  predicate DeallocRequires(k: Constants, s: Variables, ref: Reference)
  {
    && ref in s.graph
    && 0 in s.invRc && ref in s.invRc[0]
  }

  function Dealloc(k: Constants, s: Variables, ref: Reference): (s': Variables)
  requires Inv(k, s)
  requires DeallocRequires(k, s, ref)
  // ensures S.Dealloc(Ik(k), I(k, s), I(k, s'), ref)
  {
    s
      .(graph := map r | r in s.graph && r != ref :: r := s.graph[r])
      .(invRc := s.invRc[0 := s.invRc[0] - {ref}])
  }

  lemma RefinesDealloc(k: Constants, s: Variables, s': Variables, ref: Reference)
  requires Inv(k, s)
  requires DeallocRequires(k, s, ref)
  requires s' == Dealloc(k, s, ref)
  ensures Inv(k, s')
  ensures S.Dealloc(Ik(k), I(k, s), I(k, s'), ref)
  {
    assume S.Inv(Ik(k), I(k, s'));
    assume (forall r | r in s'.graph :: (
      && var c := s'.graph[r].rc;
      && c in s'.invRc
      && r in s'.invRc[c]));
    assume forall c | c in s'.invRc :: forall r | r in s'.invRc[c] :: r in s'.graph;
    assume forall c | c in s'.invRc :: forall r | r in s'.invRc[c] :: s'.graph[r].rc == c;
    assert Inv(k, s');
    assume forall r | r in I(k, s).graph :: ref !in I(k, s).graph[r];
    assert S.Dealloc(Ik(k), I(k, s), I(k, s'), ref);
  }

  predicate AttachRequires(k: Constants, s: Variables, parent: Reference, ref: Reference)
  {
    && parent in s.graph
    && ref in s.graph
    && ref !in s.graph[parent].adjList
    && parent != ref
    && s.graph[ref].rc as nat < 0x1_0000_0000_0000_0000 - 1
  }

  function Attach(k: Constants, s: Variables, parent: Reference, ref: Reference): (s': Variables)
  requires Inv(k, s)
  requires AttachRequires(k, s, parent, ref)
  // ensures S.Attach(Ik(k), I(k, s), I(k, s'), parent, ref)
  {
    var rc := s.graph[ref].rc;
    s
      .(graph := s.graph
        [parent := s.graph[parent].(adjList := (s.graph[parent].adjList + {ref}))]
        [ref := s.graph[ref].(rc := (s.graph[ref].rc + 1))]
      )
      .(invRc := s.invRc
        [rc := s.invRc[rc] - {ref}]
        [(rc + 1) := (if (rc + 1) in s.invRc then s.invRc[rc + 1] else {}) + {ref}]
      )
  }

  lemma RefinesAttach(k: Constants, s: Variables, s': Variables, parent: Reference, ref: Reference)
  requires Inv(k, s)
  requires AttachRequires(k, s, parent, ref)
  requires s' == Attach(k, s, parent, ref)
  ensures Inv(k, s')
  ensures S.Attach(Ik(k), I(k, s), I(k, s'), parent, ref)
  {
    assume S.Inv(Ik(k), I(k, s'));
    assume (forall r | r in s'.graph :: (
      && var c := s'.graph[r].rc;
      && c in s'.invRc
      && r in s'.invRc[c]));
    assume forall c | c in s'.invRc :: forall r | r in s'.invRc[c] :: r in s'.graph;
    assume forall c | c in s'.invRc :: forall r | r in s'.invRc[c] :: s'.graph[r].rc == c;
    assert Inv(k, s');
    assume I(k, s').graph == I(k, s).graph[parent := (I(k, s).graph[parent] + {ref})];
    assert S.Attach(Ik(k), I(k, s), I(k, s'), parent, ref);
  }

  predicate DetachRequires(k: Constants, s: Variables, parent: Reference, ref: Reference)
  {
    && parent in s.graph
    && ref in s.graph
    && ref in s.graph[parent].adjList
  }

  function Detach(k: Constants, s: Variables, parent: Reference, ref: Reference): (s': Variables)
  requires Inv(k, s)
  requires DetachRequires(k, s, parent, ref)
  // ensures S.Detach(Ik(k), I(k, s), I(k, s'), parent, ref)
  {
    var rc := s.graph[ref].rc;
    s
      .(graph := s.graph
        [parent := s.graph[parent].(adjList := (s.graph[parent].adjList - {ref}))]
        [ref := s.graph[ref].(rc := (s.graph[ref].rc - 1))]
      )
      .(invRc := s.invRc
        [rc := s.invRc[rc] - {ref}]
        [(rc - 1) := (if (rc - 1) in s.invRc then s.invRc[rc - 1] else {}) + {ref}]
      )
  }

  lemma RefinesDetach(k: Constants, s: Variables, s': Variables, parent: Reference, ref: Reference)
  requires Inv(k, s)
  requires DetachRequires(k, s, parent, ref)
  requires s' == Detach(k, s, parent, ref)
  ensures Inv(k, s')
  ensures S.Detach(Ik(k), I(k, s), I(k, s'), parent, ref)
  {
    assume S.Inv(Ik(k), I(k, s'));
    assume (forall r | r in s'.graph :: (
      && var c := s'.graph[r].rc;
      && c in s'.invRc
      && r in s'.invRc[c]));
    assume forall c | c in s'.invRc :: forall r | r in s'.invRc[c] :: r in s'.graph;
    assume forall c | c in s'.invRc :: forall r | r in s'.invRc[c] :: s'.graph[r].rc == c;
    assume forall ref | ref in s'.graph :: (exists r | r in s'.graph :: ref in s'.graph[r].adjList) ==> s'.graph[ref].rc > 0;
    assert Inv(k, s');
    assume I(k, s').graph == I(k, s).graph[parent := (I(k, s).graph[parent] - {ref})];
    assert S.Detach(Ik(k), I(k, s), I(k, s'), parent, ref);
  }

  datatype Step =
    | AllocStep() 
    | DeallocStep(ref: Reference)
    | AttachStep(parent: Reference, ref: Reference)
    | DetachStep(parent: Reference, ref: Reference)

  predicate NextStepRequires(k: Constants, s: Variables, step: Step)
  {
    match step {
      case AllocStep() => AllocRequires(k, s)
      case DeallocStep(ref) => DeallocRequires(k, s, ref)
      case AttachStep(parent, ref) => AttachRequires(k, s, parent, ref)
      case DetachStep(parent, ref) => DetachRequires(k, s, parent, ref)
    }
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, step: Step)
  {
    && Inv(k, s)
    && NextStepRequires(k, s, step)
    && s' == match step {
      case AllocStep() => Alloc(k, s).s'
      case DeallocStep(ref) => Dealloc(k, s, ref)
      case AttachStep(parent, ref) => Attach(k, s, parent, ref)
      case DetachStep(parent, ref) => Detach(k, s, parent, ref)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables)
  {
    exists step: Step :: NextStep(k, s, s', step)
  }

  lemma RefinesNextStep(k: Constants, s: Variables, s': Variables, step: Step)
  requires Inv(k, s)
  requires NextStep(k, s, s', step)
  ensures Inv(k, s')
  ensures S.Next(Ik(k), I(k, s), I(k, s'))
  {
    match step {
      case AllocStep() => {
        var ref := RefinesAlloc(k, s, s');
        assert S.NextStep(Ik(k), I(k, s), I(k, s'), S.AllocStep(ref));
      }
      case DeallocStep(ref) => {
        RefinesDealloc(k, s, s', ref);
        assert S.NextStep(Ik(k), I(k, s), I(k, s'), S.DeallocStep(ref));
      }
      case AttachStep(parent, ref) => {
        RefinesAttach(k, s, s', parent, ref);
        assert S.NextStep(Ik(k), I(k, s), I(k, s'), S.AttachStep(parent, ref));
      }
      case DetachStep(parent, ref) => {
        RefinesDetach(k, s, s', parent, ref);
        assert S.NextStep(Ik(k), I(k, s), I(k, s'), S.DetachStep(parent, ref));
      }
    }
  }

  lemma RefinesNext(k: Constants, s: Variables, s': Variables)
  requires Inv(k, s)
  requires Next(k, s, s')
  ensures Inv(k, s')
  ensures S.Next(Ik(k), I(k, s), I(k, s'))
  {
    var step :| NextStep(k, s, s', step);
    RefinesNextStep(k, s, s', step);
  }
}

module ImperativeGraph /* refines FunctionalGraph */ {
  import opened NativeTypes
  import opened Options
  import MutableMap
  import F = FunctionalGraph

  type HashMap<V(==)> = MutableMap.ResizingHashMap<V>
  type GraphValue = F.GraphValue
  type Reference = F.Reference

  lemma {:axiom} CountBoundedByMemory<V(==)>(h: HashMap<V>)
  requires h.Inv()
  ensures h.Count as nat < 0x10000000000000000 / 8

  class Impl {
    var graph: HashMap<GraphValue>;
    var invRc: HashMap<set<Reference>>;
    var nextRef: uint64;

    ghost var Repr: set<object>;

    constructor()
    ensures WFImpl(this)
    {
      graph := new MutableMap.ResizingHashMap<GraphValue>(1024);
      invRc := new MutableMap.ResizingHashMap<set<Reference>>(256);
      nextRef := 1;

      new;

      Repr := {this} + graph.Repr + invRc.Repr;
    }
  }

  predicate WFImpl(impl: Impl)
  ensures WFImpl(impl) ==> {impl, impl.graph, impl.invRc} <= impl.Repr
  reads impl, impl.Repr
  {
    && {impl, impl.graph, impl.invRc} <= impl.Repr
    && impl.Repr == {impl} + impl.graph.Repr + impl.invRc.Repr

    && impl.graph.Inv()
    && impl.invRc.Inv()
  }

  function Ik(impl: Impl): F.Constants
  {
    F.Constants()
  }

  function I(impl: Impl): F.Variables
  requires WFImpl(impl)
  reads impl.Repr
  {
    F.Variables(
      MutableMap.ResizingHashMap.I(impl.graph),
      MutableMap.ResizingHashMap.I(impl.invRc),
      impl.nextRef)
  }

  predicate Inv(impl: Impl)
  requires WFImpl(impl)
  reads impl.Repr
  {
    && F.Inv(Ik(impl), I(impl))
  }

  function method UnwrapOr<T>(opt: Option<T>, otherwise: T): T
  {
    match opt {
      case Some(x) => x
      case None => otherwise
    }
  }

  method Alloc(impl: Impl) returns (ref: Reference)
  requires WFImpl(impl)
  requires F.AllocRequires(Ik(impl), I(impl))
  requires Inv(impl)
  ensures WFImpl(impl)
  ensures Inv(impl)
  ensures F.Next(old(Ik(impl)), old(I(impl)), I(impl))
  modifies impl.Repr
  {
    ref := impl.nextRef;
    impl.nextRef := impl.nextRef + 1;
    CountBoundedByMemory(impl.graph);
    var _ := impl.graph.Insert(ref, F.GraphValue({}, 0));
    var invRc0opt := impl.invRc.Get(0);
    var invRc0 := UnwrapOr(invRc0opt, {}) + {ref};
    CountBoundedByMemory(impl.invRc);
    var _ := impl.invRc.Insert(0, invRc0);

    impl.Repr := {impl} + impl.graph.Repr + impl.invRc.Repr;

    ghost var ghostRef := F.RefinesAlloc(old(Ik(impl)), old(I(impl)), I(impl));
    assert ref == ghostRef;
    assert F.NextStep(old(Ik(impl)), old(I(impl)), I(impl), F.AllocStep());
  }

  method Dealloc(impl: Impl, ref: Reference)
  requires WFImpl(impl)
  requires F.DeallocRequires(Ik(impl), I(impl), ref)
  requires Inv(impl)
  ensures WFImpl(impl)
  ensures Inv(impl)
  ensures F.Next(old(Ik(impl)), old(I(impl)), I(impl))
  modifies impl.Repr
  {
    var _ := impl.graph.Remove(ref);
    var invRc0opt := impl.invRc.Get(0);
    assert invRc0opt.Some?;
    var invRc0 := invRc0opt.value - {ref};
    CountBoundedByMemory(impl.invRc);
    var _ := impl.invRc.Insert(0, invRc0);

    impl.Repr := {impl} + impl.graph.Repr + impl.invRc.Repr;

    F.RefinesDealloc(old(Ik(impl)), old(I(impl)), I(impl), ref);
    assert F.NextStep(old(Ik(impl)), old(I(impl)), I(impl), F.DeallocStep(ref));
  }

  method Attach(impl: Impl, parent: Reference, ref: Reference)
  requires WFImpl(impl)
  requires F.AttachRequires(Ik(impl), I(impl), parent, ref)
  requires Inv(impl)
  ensures WFImpl(impl)
  ensures Inv(impl)
  ensures F.Next(old(Ik(impl)), old(I(impl)), I(impl))
  modifies impl.Repr
  {
    assert impl.graph.Repr !! impl.invRc.Repr;
    assert WFImpl(impl);

    var parentEl := impl.graph.Get(parent);
    assert parentEl.Some?;
    var newParentEl := parentEl.value.(adjList := (parentEl.value.adjList + {ref}));
    CountBoundedByMemory(impl.graph);
    var _ := impl.graph.Insert(parent, newParentEl);
    impl.Repr := {impl} + impl.graph.Repr + impl.invRc.Repr;

    var refEl := impl.graph.Get(ref);
    assert refEl.Some?;
    var newRefEl := refEl.value.(rc := refEl.value.rc + 1);
    CountBoundedByMemory(impl.graph);
    var _ := impl.graph.Insert(ref, newRefEl);
    impl.Repr := {impl} + impl.graph.Repr + impl.invRc.Repr;

    var invRcAopt := impl.invRc.Get(refEl.value.rc);
    assert invRcAopt.Some?;
    var invRcA := invRcAopt.value - {ref};
    CountBoundedByMemory(impl.invRc);
    var _ := impl.invRc.Insert(refEl.value.rc, invRcA);
    impl.Repr := {impl} + impl.graph.Repr + impl.invRc.Repr;

    var invRcBopt := impl.invRc.Get(refEl.value.rc + 1);
    var invRcB := UnwrapOr(invRcBopt, {}) + {ref};
    CountBoundedByMemory(impl.invRc);
    var _ := impl.invRc.Insert(refEl.value.rc + 1, invRcB);
    impl.Repr := {impl} + impl.graph.Repr + impl.invRc.Repr;

    assert I(impl) == F.Attach(old(Ik(impl)), old(I(impl)), parent, ref);
    F.RefinesAttach(old(Ik(impl)), old(I(impl)), I(impl), parent, ref);
    assert F.NextStep(old(Ik(impl)), old(I(impl)), I(impl), F.AttachStep(parent, ref));
  }

  method Detach(impl: Impl, parent: Reference, ref: Reference)
  requires WFImpl(impl)
  requires F.DetachRequires(Ik(impl), I(impl), parent, ref)
  requires Inv(impl)
  ensures WFImpl(impl)
  ensures Inv(impl)
  ensures F.Next(old(Ik(impl)), old(I(impl)), I(impl))
  modifies impl.Repr
  {
    assert impl.graph.Repr !! impl.invRc.Repr;
    assert WFImpl(impl);

    var parentEl := impl.graph.Get(parent);
    assert parentEl.Some?;
    var newParentEl := parentEl.value.(adjList := (parentEl.value.adjList - {ref}));
    CountBoundedByMemory(impl.graph);
    var _ := impl.graph.Insert(parent, newParentEl);
    impl.Repr := {impl} + impl.graph.Repr + impl.invRc.Repr;

    var refEl := impl.graph.Get(ref);
    assert refEl.Some?;
    var newRefEl := refEl.value.(rc := refEl.value.rc - 1);
    CountBoundedByMemory(impl.graph);
    var _ := impl.graph.Insert(ref, newRefEl);
    impl.Repr := {impl} + impl.graph.Repr + impl.invRc.Repr;

    var invRcAopt := impl.invRc.Get(refEl.value.rc);
    assert invRcAopt.Some?;
    var invRcA := invRcAopt.value - {ref};
    CountBoundedByMemory(impl.invRc);
    var _ := impl.invRc.Insert(refEl.value.rc, invRcA);
    impl.Repr := {impl} + impl.graph.Repr + impl.invRc.Repr;

    var invRcBopt := impl.invRc.Get(refEl.value.rc - 1);
    var invRcB := UnwrapOr(invRcBopt, {}) + {ref};
    CountBoundedByMemory(impl.invRc);
    var _ := impl.invRc.Insert(refEl.value.rc - 1, invRcB);
    impl.Repr := {impl} + impl.graph.Repr + impl.invRc.Repr;

    assert I(impl) == F.Detach(old(Ik(impl)), old(I(impl)), parent, ref);
    F.RefinesDetach(old(Ik(impl)), old(I(impl)), I(impl), parent, ref);
    assert F.NextStep(old(Ik(impl)), old(I(impl)), I(impl), F.DetachStep(parent, ref));
  }
}
