include "../lib/Maps.dfy"
include "../lib/sequences.dfy"
  
abstract module BlockInterface {
  import opened Sequences
  import opened Maps
    
  type Reference(!new,==) // LBA

  type View<T> = imap<Reference, T>
  type ReferenceGraph = imap<Reference, iset<Reference>>

  function Root(k: Constants) : Reference

  type Constants
  datatype Variables<T> = Variables(view: imap<Reference, T>, refGraph: ReferenceGraph)

  predicate RefGraphIsClosed(k: Constants, s: Variables) {
    forall key :: key in s.refGraph ==> s.refGraph[key] <= s.refGraph.Keys
  }

  predicate ViewAndRefGraphAreConsistent(k: Constants, s: Variables) {
    s.view.Keys == s.refGraph.Keys
  }
  
  type Lookup = seq<Reference>

  predicate IsPath(k: Constants, s: Variables, lookup: Lookup)
  {
    && (forall i :: 0 <= i < |lookup| ==> lookup[i] in s.refGraph)
    && (forall i :: 0 <= i < |lookup|-1 ==> lookup[i+1] in s.refGraph[lookup[i]])
  }

  predicate IsCycle(k: Constants, s: Variables, lookup: Lookup) {
    && 0 < |lookup|
    && IsPath(k, s, lookup)
    && lookup[0] in s.refGraph[Last(lookup)]
  }

  // We don't maintain this as an invariant, but some refinements
  // might want to add this invariant so that they can use a
  // reference-counting garbage collection algorithm.  For that, we
  // require that no cycle exists anywhere, even in unreachable (from
  // the root) components of the graph.
  predicate Acyclic(k: Constants, s: Variables) {
    forall lookup :: IsPath(k, s, lookup) ==> !IsCycle(k, s, lookup)
  }
  
  predicate LookupIsValid(k: Constants, s: Variables, lookup: Lookup)
  {
    && |lookup| > 0
    && lookup[0] == Root(k)
    && IsPath(k, s, lookup)
  }

  predicate ReachableReference(k: Constants, s: Variables, ref: Reference)
  {
    exists lookup :: LookupIsValid(k, s, lookup) && Last(lookup) == ref
  }

  function LiveReferences(k: Constants, s: Variables) : iset<Reference> {
    iset ref | ReachableReference(k, s, ref)
  }

  predicate LiveDataAvailable(k: Constants, s: Variables) {
    LiveReferences(k, s) <= s.view.Keys
  }

  function Read<T>(k: Constants, s: Variables, ref: Reference) : T
    requires LiveDataAvailable(k, s)
    requires ref in s.view
  {
    s.view[ref]
  }
    
  predicate Init<T>(k: Constants, s: Variables, block: T) {
    && s.view == imap[Root(k) := block]
    && s.refGraph == imap[Root(k) := iset{}]
  }

  predicate Alloc<T>(k: Constants, s: Variables, s': Variables, block: T, successors: iset<Reference>, ref: Reference) {
    && successors <= s.view.Keys
    && ref !in s.view

    && s'.refGraph == s.refGraph[ref := successors]
    && s'.view == s.view[ref := block]
  }
    
  predicate Write<T>(k: Constants, s: Variables, s': Variables, ref: Reference, block: T, successors: iset<Reference>) {
    && successors <= s.view.Keys
    && ref in s.view

    && s'.refGraph == s.refGraph[ref := successors]
    && s'.view == s.view[ref := block]
  }

  predicate IsStatePath(k: Constants, s: Variables, s': Variables, steps: seq<Step>, path: seq<Variables>)
    decreases steps, 0
  {
    && |path| == |steps| + 1
    && path[0] == s
    && Last(path) == s'
    && (forall i :: 0 <= i < |steps| ==> NextStep(k, path[i], path[i+1], steps[i]))
  }

  predicate ValidTransaction(steps: seq<Step>)
  {
    && (forall i :: 0 <= i < |steps| ==> steps[i].AllocStep? || steps[i].WriteStep?)
  }

  lemma Transaction2Steps(k: Constants, s: Variables, s': Variables, steps: seq<Step>)
  decreases steps, 1
  ensures (
    && 0 < |steps|
    && ValidTransaction(steps)
    && (exists path: seq<Variables> :: IsStatePath(k, s, s', steps, path))
    &&|steps| == 2
  ) ==>
      exists sint ::
      && NextStep(k, s, sint, steps[0])
      && NextStep(k, sint, s', steps[1])
  {
    if (
        && 0 < |steps|
        && ValidTransaction(steps)
        && (exists path: seq<Variables> :: IsStatePath(k, s, s', steps, path))
        &&|steps| == 2)
    {
      var path :| IsStatePath(k, s, s', steps, path);
      var sint := path[1];
      assert NextStep(k, s, sint, steps[0]);
      assert NextStep(k, sint, s', steps[1]);
    }
  }

  lemma Transaction3Steps(k: Constants, s: Variables, s': Variables, steps: seq<Step>)
  decreases steps, 1
  ensures (
    && 0 < |steps|
    && ValidTransaction(steps)
    && (exists path: seq<Variables> :: IsStatePath(k, s, s', steps, path))
    &&|steps| == 3
  ) ==>
      exists sint, sint' ::
      && NextStep(k, s, sint, steps[0])
      && NextStep(k, sint, sint', steps[1])
      && NextStep(k, sint', s', steps[2])
  {
    if (
        && 0 < |steps|
        && ValidTransaction(steps)
        && (exists path: seq<Variables> :: IsStatePath(k, s, s', steps, path))
        &&|steps| == 3)
    {
      var path :| IsStatePath(k, s, s', steps, path);
      var sint := path[1];
      var sint' := path[2];
      assert NextStep(k, s, sint, steps[0]);
      assert NextStep(k, sint, sint', steps[1]);
      assert NextStep(k, sint', s', steps[2]);
    }
  }

  
  predicate Transaction<T(!new)>(k: Constants, s: Variables, s': Variables, steps: seq<Step>)
    decreases steps, 2
    ensures Transaction(k, s, s', steps) && |steps| == 2 ==> exists sint ::
      && NextStep(k, s, sint, steps[0])
      && NextStep(k, sint, s', steps[1])
    ensures Transaction(k, s, s', steps) && |steps| == 3 ==> exists sint, sint' ::
      && NextStep(k, s, sint, steps[0])
      && NextStep(k, sint, sint', steps[1])
      && NextStep(k, sint', s', steps[2])
  {
    Transaction2Steps(k, s, s', steps);
    Transaction3Steps(k, s, s', steps);
    && 0 < |steps|
    && ValidTransaction(steps)
    && (exists path: seq<Variables> :: IsStatePath(k, s, s', steps, path))
  }

  function Predecessors(refGraph: ReferenceGraph, ref: Reference) : iset<Reference> {
    iset ref1 | ref1 in refGraph && ref in refGraph[ref1]
  }
  
  predicate ClosedUnderPredecessor(refGraph: ReferenceGraph, refs: iset<Reference>) {
    forall ref :: ref in refs ==> Predecessors(refGraph, ref) <= refs
  }
   
  predicate GC(k: Constants, s: Variables, s': Variables, refs: iset<Reference>) {
    && refs !! LiveReferences(k, s)
    && refs <= s.view.Keys
    && ClosedUnderPredecessor(s.refGraph, refs)
    
    && s'.view == IMapRemove(s.view, refs)
    && s'.refGraph == IMapRemove(s.refGraph, refs)
  }
  
  datatype Step<T> =
    | AllocStep(block: T, successors: iset<Reference>, ref: Reference)
    | WriteStep(ref: Reference, block: T, successors: iset<Reference>)
    | TransactionStep(steps: seq<Step>)
    | GCStep(refs: iset<Reference>)
    
  predicate NextStep(k: Constants, s: Variables, s': Variables, step: Step)
    decreases step
  {
    match step {
      case AllocStep(block, successors, ref) => Alloc(k, s, s', block, successors, ref)
      case WriteStep(ref, block, successors) => Write(k, s, s', ref, block, successors)
      case TransactionStep(steps) => Transaction(k, s, s', steps)
      case GCStep(refs) => GC(k, s, s', refs)
    }
  }
    
  predicate Next<T(!new)>(k: Constants, s: Variables, s': Variables) {
    exists step :: NextStep(k, s, s', step)
  }

  /////////// Some helper facts

  function AllocatedReferences(steps: seq<Step>) : iset<Reference>
    requires ValidTransaction(steps)
  {
    //iset ref | (exists i :: 0 <= i < |steps| && steps[i].AllocStep? && steps[i].ref == ref)
    if |steps| == 0 then iset{}
    else
      (if steps[0].AllocStep? then iset{steps[0].ref} else iset{}) + AllocatedReferences(steps[1..])
  }

  function LocallyReachableReferences(k: Constants, s: Variables, p: Reference) : iset<Reference>
  {
    // p, it's children, and it's grandchildren
    iset path |
    && IsPath(k, s, path)
    && 1 < |path| <= 3
    && path[0] == p
    :: Last(path)
  }

  function NewlyReachableReferences(k: Constants, s: Variables, s': Variables, p: Reference) : iset<Reference>
  {
    iset path |
      && IsPath(k, s', path)
      && 0 < |path|
      && path[0] == p
      && (forall i :: 0 < i < |path| - 1 ==> path[i] in s'.view.Keys - s.view.Keys)
      && Last(path) in s.view
      :: Last(path)
  }

  predicate EditIsLocal(k: Constants, s: Variables, s': Variables, p: Reference)
    requires ViewAndRefGraphAreConsistent(k, s)
    requires ViewAndRefGraphAreConsistent(k, s')
  {
    && (forall ref :: ref in s.view.Keys * s'.view.Keys - iset{p} ==> s.refGraph[ref] == s'.refGraph[ref])
    && NewlyReachableReferences(k, s, s', p) <= LocallyReachableReferences(k, s, p)
  }

  predicate NewNodesAreCycleFree(k: Constants, s: Variables, s': Variables)
  {
    forall path ::
      && IsPath(k, s', path)
      && (forall i :: 0 <= i < |path| ==> path[i] in s'.view.Keys - s.view.Keys)
      ==> !IsCycle(k, s', path)
  }

  function FirstInView(path: Lookup, view: View) : (pos: int)
    requires exists i :: 0 <= i < |path| && path[i] in view
    ensures 0 <= pos < |path|
    ensures path[pos] in view
    ensures forall i :: 0 <= i < pos ==> path[i] !in view
  {
    if path[0] in view then 0
    else 1 + FirstInView(path[1..], view)
  }

function UndoLocalEdit(k: Constants, s: Variables, s': Variables, p: Reference, path: Lookup) : (result: Lookup)
    requires ViewAndRefGraphAreConsistent(k, s)
    requires ViewAndRefGraphAreConsistent(k, s')
    requires RefGraphIsClosed(k, s)
    requires 1 < |path|
    requires path[0] in s.view.Keys
    requires Last(path) in s.view.Keys
    requires EditIsLocal(k, s, s', p)
    requires NewNodesAreCycleFree(k, s, s')
    requires IsPath(k, s', path)
    ensures 0 < |result| 
    ensures IsPath(k, s, result)
    ensures result[0] == path[0]
    ensures Last(result) == Last(path)
  {
    if path[0] == p then
      var len := 1 + FirstInView(path[1..], s.view);
      var prefix := path[..len];
      var successor := path[len];
      var wit := prefix + [successor];
      assert Last(wit) in s.view;
      assert successor in NewlyReachableReferences(k, s, s', p);
      var replacement :|
        && 1 < |replacement|
        && IsPath(k, s, replacement)
        && replacement[0] == path[0]
        && successor == Last(replacement);
      if len < |path| - 1 then DropLast(replacement) + UndoLocalEdit(k, s, s', p, path[len..]) else replacement
    else if |path| == 2 then path
    else path[..1] + UndoLocalEdit(k, s, s', p, path[1..])
  }
  
  lemma LocalEditPreservesAcyclic(k: Constants, s: Variables, s': Variables, p: Reference)
    requires ViewAndRefGraphAreConsistent(k, s)
    requires ViewAndRefGraphAreConsistent(k, s')
    requires RefGraphIsClosed(k, s)
    requires Acyclic(k, s)
    requires EditIsLocal(k, s, s', p)
    requires NewNodesAreCycleFree(k, s, s')
    ensures Acyclic(k, s')
  {
    if cycle :| IsCycle(k, s', cycle) {
      var i :| 0 <= i < |cycle| && cycle[i] in s.view;
      var rcycle := cycle[i..] + cycle[..i];
      assert IsCycle(k, s', rcycle)  && rcycle[0] in s.view;
      var path := rcycle + [rcycle[0]];
      var rpath := UndoLocalEdit(k, s, s', p, path);
      assert IsCycle(k, s, DropLast(rpath));
    }
  }
  
  /////////// Invariants

  predicate Inv(k: Constants, s: Variables) {
    && Root(k) in s.view // Redundant? (yes, but can we delete it?)
    && ViewAndRefGraphAreConsistent(k, s)
    && RefGraphIsClosed(k, s)
    && LiveDataAvailable(k, s)
  }

  lemma AllocPreservesInv<T>(k: Constants, s: Variables, s': Variables, block: T, successors: iset<Reference>, ref: Reference)
    requires Inv(k, s)
    requires Alloc(k, s, s', block, successors, ref)
    ensures Inv(k, s')
  {
  }
  
  lemma WritePreservesInv<T>(k: Constants, s: Variables, s': Variables, ref: Reference, block: T, successors: iset<Reference>)
    requires Inv(k, s)
    requires Write(k, s, s', ref, block, successors)
    ensures Inv(k, s')
  {
  }

  lemma TransactionPreservesInv(k: Constants, s: Variables, s': Variables, steps: seq<Step>)
    requires Inv(k, s)
    requires Transaction(k, s, s', steps)
    ensures Inv(k, s')
    decreases steps
  {
    var path :| IsStatePath(k, s, s', steps, path);
    var i := 0;
    while i < |steps|
      invariant 0 <= i <= |steps|
      invariant forall j :: 0 <= j <= i ==> Inv(k, path[j])
    {
      NextStepPreservesInv(k, path[i], path[i+1], steps[i]);
      i := i + 1;
    }
  }

  lemma GCPreservesInv(k: Constants, s: Variables, s': Variables, refs: iset<Reference>)
    requires Inv(k, s)
    requires GC(k, s, s', refs)
    ensures Inv(k, s')
  {
    assert LookupIsValid(k, s, [Root(k)]);
  }

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, step: Step)
    requires Inv(k, s)
    requires NextStep(k, s, s', step)
    ensures Inv(k, s')
    decreases step
  {
    match step {
      case AllocStep(block, successors, ref) => AllocPreservesInv(k, s, s', block, successors, ref);
      case WriteStep(ref, block, successors) => WritePreservesInv(k, s, s', ref, block, successors);
      case TransactionStep(steps) => TransactionPreservesInv(k, s, s', steps);
      case GCStep(ref) => GCPreservesInv(k, s, s', ref);
    }
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables)
    requires Inv(k, s)
    requires Next(k, s, s')
    ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', step);
    NextStepPreservesInv(k, s, s', step);
  }
}
