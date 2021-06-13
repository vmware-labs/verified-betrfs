// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/Maps.i.dfy"
include "../lib/Base/Sequences.i.dfy"
include "../MapSpec/MapSpec.s.dfy"
include "../Betree/Betree.i.dfy"
//
// Invariants about Betrees: lookup structure, non-equivocation, and
// preservation. 
// TODO(jonh) and apparently a bunch of dead code! See TODO inline.
//
  
module BetreeInv {
  import opened B = Betree
  import opened Maps
  import opened Sequences
  import opened BetreeSpec`Internal
  import opened G = BetreeSpec.G
  import opened Options
  import opened KeyType
  import opened ValueType
  import UI

  predicate LookupRespectsView(view: BI.View, lookup: Lookup) {
    forall i :: 0 <= i < |lookup| ==> IMapsTo(view, lookup[i].readOp.ref, lookup[i].readOp.node)
  }

  predicate IsPathLookup(view: BI.View, lookup: Lookup) {
    && |lookup| > 0
    && LookupRespectsView(view, lookup)
    && LookupFollowsChildRefs(lookup)
    && LookupFollowsEdges(lookup)
  }

  predicate IsSatisfyingLookup(view: BI.View, key: Key, value: Value, lookup: Lookup) {
    && IsPathLookup(view, lookup)
    && lookup[0].currentKey == key
    && LookupVisitsWFNodes(lookup)
    && BufferDefinesValue(InterpretLookup(lookup), value)
  }

  predicate IsSatisfyingLookupFrom(view: BI.View, key: Key, value: Value, lookup: Lookup, start: Reference) {
    && IsSatisfyingLookup(view, key, value, lookup)
    && lookup[0].readOp.ref == start
  }

  predicate KeyHasSatisfyingLookup(view: BI.View, key: Key, start: Reference)
  {
    exists lookup: Lookup, value ::
      && IsSatisfyingLookupFrom(view, key, value, lookup, start)
  }

  function PathOfLookup(lookup: Lookup) : (path : G.Path)
    ensures |path| == |lookup|
    ensures forall i :: 0 <= i < |path| ==> path[i] == lookup[i].readOp.ref
  {
    if lookup == [] then []
    else PathOfLookup(DropLast(lookup)) + [Last(lookup).readOp.ref]
  }
  
  predicate LookupIsAcyclic(lookup: Lookup) {
    forall i, j :: 0 <= i < |lookup| && 0 <= j < |lookup| && i != j ==> lookup[i].readOp.ref != lookup[j].readOp.ref
  }

  predicate Acyclic(s: Variables) {
    forall lookup ::
      IsPathLookup(s.bcv.view, lookup) ==>
      LookupIsAcyclic(lookup)
  }

  predicate Inv(s: Variables)
  {
    && BI.Inv(s.bcv)
    && G.IsAcyclic(s.bcv.view)
    && Acyclic(s)
    && (forall key | MS.InDomain(key) :: KeyHasSatisfyingLookup(s.bcv.view, key, Root()))
    && BI.RootHasNoPredecessor(s.bcv.view)
  }

  //// Definitions for lookup preservation

  // One-way preservation

  predicate PreservesLookups(s: Variables, s': Variables, start: Reference)
  {
    forall lookup: Lookup, key, value :: IsSatisfyingLookupFrom(s.bcv.view, key, value, lookup, start) ==>
      exists lookup': Lookup :: IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start)
  }

  predicate PreservesLookupsExcept(s: Variables, s': Variables, start: Reference, exceptQuery: Key)
  {
    forall lookup: Lookup, key, value :: key != exceptQuery && IsSatisfyingLookupFrom(s.bcv.view, key, value, lookup, start) ==>
      exists lookup': Lookup :: IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start)
  }

  predicate PreservesLookupsExceptRange(s: Variables, s': Variables, exceptMap: iset<Key>)
  {
    forall lookup, key, value :: key !in exceptMap && IsSatisfyingLookupFrom(s.bcv.view, key, value, lookup, Root()) ==>
      exists lookup' :: IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', Root())
  }

  // TODO generalize this to explain how the value changes when a non-Define
  // message is inserted
  predicate PreservesLookupsPut(s: Variables, s': Variables, key: Key, value: Value)
  {
    && PreservesLookupsExcept(s, s', Root(), key)
    && exists lookup: Lookup :: IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup, Root())
  }

  lemma InterpsEqualIfAllBuffersEqual(a: Lookup, b: Lookup)
  requires LookupVisitsWFNodes(a);
  requires LookupVisitsWFNodes(b);
  requires |a| == |b|
  requires forall j | 0 <= j < |a| :: a[j].readOp.node.buffer[a[j].currentKey] == b[j].readOp.node.buffer[b[j].currentKey]
  ensures InterpretLookup(a) == InterpretLookup(b)
  {
    if |a| == 0 {
    } else {
      InterpsEqualIfAllBuffersEqual(DropLast(a), DropLast(b));
    }
  }

  lemma {:induction true} InterpretLookupAdditive(a: Lookup, b: Lookup)
  requires LookupVisitsWFNodes(a);
  requires LookupVisitsWFNodes(b);
  ensures InterpretLookup(a + b) == G.M.Merge(InterpretLookup(a), InterpretLookup(b))
  {
    if |b| == 0 {
      assert a + b == a;
    } else {
      assert a + b == a + DropLast(b) + [Last(b)]; // observe
      assert forall l: Lookup :: |l| == 1 && LookupVisitsWFNodes(l) ==> InterpretLookup(l) == l[0].readOp.node.buffer[l[0].currentKey]; // observe
      G.M.MergeIsAssociative(InterpretLookup(a), InterpretLookup(DropLast(b)), InterpretLookup([Last(b)]));
    }
  }

  lemma InterpretLookupAdditive3(a: Lookup, b: Lookup, c: Lookup)
  requires LookupVisitsWFNodes(a);
  requires LookupVisitsWFNodes(b);
  requires LookupVisitsWFNodes(c);
  ensures InterpretLookup(a + b + c) == G.M.Merge(G.M.Merge(InterpretLookup(a), InterpretLookup(b)), InterpretLookup(c))
  {
    InterpretLookupAdditive(a + b, c); // a + b
    InterpretLookupAdditive(a, b); // a + b
  }


  // CantEquivocate
  // It's a lemma here (follows from structure of Lookups) - not an invariant!

  lemma SatisfyingLookupsForKeyAgree(s: Variables, key: Key, value: Value, value': Value, lookup: Lookup, lookup': Lookup, idx: int)
  requires IsSatisfyingLookup(s.bcv.view, key, value, lookup);
  requires IsSatisfyingLookup(s.bcv.view, key, value', lookup');
  requires 0 <= idx < |lookup|;
  requires 0 <= idx < |lookup'|;
  requires lookup[0].readOp.ref == lookup'[0].readOp.ref
  ensures lookup[idx] == lookup'[idx];
  {
    if (idx == 0) {
    } else {
      SatisfyingLookupsForKeyAgree(s, key, value, value', lookup, lookup', idx - 1);
      assert LookupFollowsChildRefAtLayer(lookup, idx-1);
      assert LookupFollowsChildRefAtLayer(lookup', idx-1);
      assert LookupFollowsEdgeAtLayer(lookup, idx-1);
      assert LookupFollowsEdgeAtLayer(lookup', idx-1);
    }
  }

  lemma CantEquivocateWlog(s: Variables, key: Key, value: Value, value': Value, lookup: Lookup, lookup': Lookup)
  requires IsSatisfyingLookup(s.bcv.view, key, value, lookup);
  requires IsSatisfyingLookup(s.bcv.view, key, value', lookup');
  requires |lookup| <= |lookup'|
  requires lookup[0].readOp.ref == lookup'[0].readOp.ref
  ensures value == value';
  {

    var junk := lookup'[|lookup|..];
    forall idx | 0 <= idx < |lookup|
    ensures lookup'[idx] == lookup[idx];
    {
        SatisfyingLookupsForKeyAgree(s, key, value, value', lookup, lookup', idx);
    }
    assert lookup' == lookup + junk; // observe
    InterpretLookupAdditive(lookup, junk);
  }

  lemma CantEquivocate(s: Variables, key: Key, value: Value, value': Value, lookup: Lookup, lookup': Lookup)
  requires IsSatisfyingLookup(s.bcv.view, key, value, lookup);
  requires IsSatisfyingLookup(s.bcv.view, key, value', lookup');
  requires lookup[0].readOp.ref == lookup'[0].readOp.ref
  ensures value == value';
  {
    if (|lookup| <= |lookup'|) {
      CantEquivocateWlog(s, key, value, value', lookup, lookup');
    } else {
      CantEquivocateWlog(s, key, value', value, lookup', lookup);
    }
  }

  // Old definitions
  // TODO clean these up; remove them or change them to use BetreeStep objects instead

  predicate InsertMessage(s: BI.Variables, s': BI.Variables, ins: MessageInsertion)
  {
    && ValidInsertion(ins)
    && BI.Reads(s, InsertionReads(ins))
    && BI.OpTransaction(s, s', InsertionOps(ins))
  }

  predicate Flush(s: BI.Variables, s': BI.Variables, flush:NodeFlush)
  {
    && ValidFlush(flush)
    && BI.Reads(s, FlushReads(flush))
    && BI.OpTransaction(s, s', FlushOps(flush))
  }

  predicate Grow(s: BI.Variables, s': BI.Variables, growth: RootGrowth)
  {
    && ValidGrow(growth)
    && BI.Reads(s, GrowReads(growth))
    && BI.OpTransaction(s, s', GrowOps(growth))
  }

  predicate Redirect(s: BI.Variables, s': BI.Variables, redirect: Redirect)
  {
    reveal_ValidRedirect();
    && ValidRedirect(redirect)
    && BI.Reads(s, RedirectReads(redirect))
    && BI.OpTransaction(s, s', RedirectOps(redirect))
  }

  predicate Query(s: BI.Variables, s': BI.Variables, q: LookupQuery)
  {
    && ValidQuery(q)
    && BI.Reads(s, QueryReads(q))
    && BI.OpTransaction(s, s', QueryOps(q))
  }

  predicate SuccQuery(s: BI.Variables, s': BI.Variables, q: SuccQuery)
  {
    && ValidSuccQuery(q)
    && BI.Reads(s, SuccQueryReads(q))
    && BI.OpTransaction(s, s', SuccQueryOps(q))
  }

  predicate Clone(s: BI.Variables, s': BI.Variables, clone: Clone)
  {
    && ValidClone(clone)
    && BI.Reads(s, CloneReads(clone))
    && BI.OpTransaction(s, s', CloneOps(clone))
  }

  //
  // Acyclicity proofs
  //
  
  lemma AcyclicGraphImpliesAcyclic(s: Variables)
    requires IsAcyclic(s.bcv.view)
    ensures Acyclic(s)
  {
    var g := s.bcv.view;
    forall lookup: Lookup | IsPathLookup(s.bcv.view, lookup)
      ensures LookupIsAcyclic(lookup)
    {
      var path := PathOfLookup(lookup);
      forall i | 0 <= i < |path|-1
        ensures path[i] in g && path[i+1] in Successors(g[path[i]])
      {
        assert LookupFollowsChildRefAtLayer(lookup, i);
      }
      G.AcyclicGraphImpliesSimplePath(g, path);
    }
  }

  lemma FlushPreservesAcyclic(s: Variables, s': Variables, flush:NodeFlush)
    requires Inv(s)
    requires Flush(s.bcv, s'.bcv, flush)
    ensures G.IsAcyclic(s'.bcv.view)
    ensures Acyclic(s')
  {
    var f := flush;
    // contradiction, no newly reachable references from parentref
    forall ref | ref in G.NewlyReachableReferences(s.bcv.view, s'.bcv.view, f.parentref)
      ensures ref in G.ReachableReferences(s.bcv.view, f.parentref)
      {
        // try to find a path that only exists in the new view
        var path :| G.NewPath(s.bcv.view, s'.bcv.view, f.parentref, path) && Last(path) == ref;
        if |path| == 2 {
          assert path[1] == ref;
          var key :| key in f.newparent.children && f.newparent.children[key].ref == ref;
          assert key !in flush.movedkeys;
          assert G.IsPath(s.bcv.view, [f.parentref, ref]);
        } else {
          assert path[|path|-2] == f.newchildref;
          assert G.IsPath(s.bcv.view, [f.parentref, f.childref, ref]);
        }
      }
    G.LocalEditPreservesAcyclic(s.bcv.view, s'.bcv.view, f.parentref);
    AcyclicGraphImpliesAcyclic(s');
  }

  lemma FlushPreservesRootHasNoPred(s: Variables, s': Variables, flush: NodeFlush)
    requires Inv(s)
    requires Flush(s.bcv, s'.bcv, flush);
    ensures BI.RootHasNoPredecessor(s'.bcv.view)
  {
    forall ref | ref in s'.bcv.view
    ensures G.Root() !in G.Successors(s'.bcv.view[ref])
    {
      if ref == flush.parentref {
        if G.Root() in G.Successors(s'.bcv.view[ref]) {
          var key : Key :| (
              && ChildMapsToRef(flush.newparent.children, key, G.Root())
              && key in flush.parent.children
              && key in flush.movedkeys );
          assert flush.parent.children[key].ref == flush.childref;
        }
      }
    }
  }

  lemma GrowPreservesAcyclic(s: Variables, s': Variables, growth: RootGrowth)
    requires Inv(s)
    requires Grow(s.bcv, s'.bcv, growth)
    ensures G.IsAcyclic(s'.bcv.view)
    ensures Acyclic(s')
  {
    forall ref | ref in G.NewlyReachableReferences(s.bcv.view, s'.bcv.view, Root())
      ensures ref in G.ReachableReferences(s.bcv.view, Root())
    {
      var path :| G.NewPath(s.bcv.view, s'.bcv.view, Root(), path) && Last(path) == ref;
      assert path[|path|-2] == growth.newchildref;
      assert G.IsPath(s.bcv.view, [Root(), ref]);
     }
    G.LocalEditPreservesAcyclic(s.bcv.view, s'.bcv.view, Root());
    AcyclicGraphImpliesAcyclic(s');
  }

  lemma RedirectResultingGraphAfterAllocs(s: BI.Variables, s': BI.Variables, childrefs: seq<Reference>, children: imap<Reference, Node>)
  requires forall ref :: ref in childrefs ==> ref in children
  requires BI.Inv(s)
  requires BI.OpTransaction(s, s', RedirectChildAllocs(childrefs, children))
  ensures BI.Inv(s')
  ensures forall childref | childref in childrefs :: IMapsTo(s'.view, childref, children[childref])
  ensures forall childref | childref in childrefs :: childref !in s.view
  ensures s.view.Keys <= s'.view.Keys
  ensures s'.view.Keys - s.view.Keys == (iset r | r in childrefs)
  ensures forall ref | ref in s.view :: IMapsTo(s'.view, ref, s.view[ref])
  decreases |childrefs|
  {
    if |childrefs| == 0 {
    } else {
      var ops := RedirectChildAllocs(childrefs, children);
      var smid := BI.GetPenultimateState(s, s', ops);
      RedirectResultingGraphAfterAllocs(s, smid, DropLast(childrefs), children);
      assert s'.view.Keys - s.view.Keys
          == (smid.view.Keys + iset{Last(childrefs)}) - s.view.Keys
          == (smid.view.Keys - s.view.Keys) + iset{Last(childrefs)}
          == (iset r | r in DropLast(childrefs)) + iset{Last(childrefs)}
          == (iset r | r in childrefs);
    }
  }

  lemma RedirectResultingGraph(s: Variables, s': Variables, redirect: Redirect)
  requires Inv(s);
  requires Redirect(s.bcv, s'.bcv, redirect);
  ensures IMapsTo(s'.bcv.view, redirect.parentref, redirect.new_parent);
  ensures forall childref | childref in redirect.new_childrefs :: IMapsTo(s'.bcv.view, childref, redirect.new_children[childref])
  ensures forall childref | childref in redirect.new_childrefs :: childref !in s.bcv.view
  ensures s'.bcv.view.Keys - s.bcv.view.Keys == redirect.new_children.Keys
  ensures forall ref | ref in s.bcv.view && ref != redirect.parentref :: IMapsTo(s'.bcv.view, ref, s.bcv.view[ref])
  {
    reveal_RedirectReads();
    reveal_RedirectOps();
    var ops := RedirectOps(redirect);
    var smid := BI.GetPenultimateState(s.bcv, s'.bcv, ops);
    RedirectResultingGraphAfterAllocs(s.bcv, smid, redirect.new_childrefs, redirect.new_children);
    assert s'.bcv.view.Keys == smid.view.Keys;
  }

  lemma ValidRedirectNewGrandchildrenGetKey(redirect: Redirect, childref: Reference, edge: Edge)
  returns (key: Key) 
  requires WFRedirect(redirect)
  requires ValidRedirectNewParent(redirect)
  requires ValidRedirectNewChildren(redirect)
  requires ValidRedirectNewGrandchildren(redirect)
  requires childref in redirect.new_children
  requires edge in redirect.new_children[childref].children.Values
  ensures ValidRedirectNewGrandchildrenCheckKey(redirect, key, childref, edge.ref)
  {
    reveal_ValidRedirectNewGrandchildren();
    var k :| ValidRedirectNewGrandchildrenCheckKey(redirect, k, childref, edge.ref);
    return k;
  }

  lemma RedirectParentInViews(s: Variables, s': Variables, redirect: Redirect)
  requires Inv(s)
  requires Redirect(s.bcv, s'.bcv, redirect)
  ensures redirect.parentref in s.bcv.view
  ensures redirect.parentref in s'.bcv.view
  ensures redirect.old_parent == s.bcv.view[redirect.parentref]
  ensures redirect.new_parent == s'.bcv.view[redirect.parentref]
  {
    RedirectResultingGraph(s, s', redirect);
    reveal_RedirectReads();
  }

  lemma RedirectOldChildInView(s: Variables, s': Variables, redirect: Redirect, old_childref: Reference)
  requires Inv(s)
  requires Redirect(s.bcv, s'.bcv, redirect)
  requires old_childref in redirect.old_childrefs 
  ensures old_childref in s.bcv.view
  ensures redirect.old_children[old_childref] == s.bcv.view[old_childref]
  {
    RedirectResultingGraph(s, s', redirect);
    reveal_RedirectReads();

    var i :| 0 <= i < |redirect.old_childrefs| && redirect.old_childrefs[i] == old_childref;
    assert BI.ReadStep(s.bcv, RedirectReads(redirect)[i+1]);
  }

  lemma RedirectOnlyPredOfChildIsParent(s: Variables, s': Variables, redirect: Redirect, parentref: Reference, ref: Reference)
  requires Inv(s);
  requires Redirect(s.bcv, s'.bcv, redirect);
  requires ref in redirect.new_children
  requires parentref in s'.bcv.view
  requires ref in Successors(s'.bcv.view[parentref])
  ensures parentref == redirect.parentref
  {
    RedirectResultingGraph(s, s', redirect);

    if (parentref == redirect.parentref) {
    } else if (parentref in redirect.new_children.Keys) {
      assert ref in redirect.new_children.Keys;
      assert ref in Successors(s'.bcv.view[parentref]);
      assert ref !in s.bcv.view;

      // find key and edge that goes from parent => parentref => ref, then find its old path
      var edge :| edge in s'.bcv.view[parentref].children.Values && edge.ref == ref;
      assert edge in redirect.new_children[parentref].children.Values;
      var key := ValidRedirectNewGrandchildrenGetKey(redirect, parentref, edge);
      var old_childref := redirect.old_parent.children[key].ref;

      RedirectOldChildInView(s, s', redirect, old_childref);
      assert ref in Successors(s.bcv.view[old_childref]);
      assert ref in s.bcv.view;
      assert false;
    } else {
      assert false;
    }
  }

  lemma RedirectNewPathReachableFromOldPath(s: Variables, s': Variables, redirect: Redirect, path: Path, ref: Reference) returns (path': Path)
    requires Inv(s)
    requires Redirect(s.bcv, s'.bcv, redirect)
    requires |path| > 2
    requires ref in G.NewlyReachableReferences(s.bcv.view, s'.bcv.view, redirect.parentref)
    requires G.NewPath(s.bcv.view, s'.bcv.view, redirect.parentref, path) && Last(path) == ref
    ensures |path'| > 1
    ensures path'[0] == redirect.parentref
    ensures Last(path') == ref
    ensures G.IsPath(s.bcv.view, path')
  {
    RedirectResultingGraph(s, s', redirect);
    assert Last(path) == ref;

    // finds the node that makes up this new path
    var new_childref := path[|path|-2];
    var new_child := redirect.new_children[new_childref];

    var edge :| edge in new_child.children.Values && edge.ref == ref;
    var key := ValidRedirectNewGrandchildrenGetKey(redirect, new_childref, edge);
    var old_childref := redirect.old_parent.children[key].ref;

    assert key in redirect.keys && key in redirect.old_parent.children;
    assert old_childref in Successors(redirect.old_parent);

    var old_child := redirect.old_children[old_childref];
    assert ref in Successors(old_child);

    RedirectParentInViews(s, s', redirect);
    assert s.bcv.view[redirect.parentref] == redirect.old_parent;
    RedirectOldChildInView(s, s', redirect, old_childref);
    assert s.bcv.view[old_childref] == old_child;

    path' := [redirect.parentref, old_childref, ref];
    assert path'[0] in s.bcv.view;
    assert path'[1] in s.bcv.view;
    assert path'[1] in Successors(s.bcv.view[path'[0]]);
    assert path'[2] in Successors(s.bcv.view[path'[1]]);
    assert G.IsPath(s.bcv.view, path');
  }

  lemma {:timeLimitMultiplier 2} RedirectPreservesAcyclic(s: Variables, s': Variables, redirect: Redirect)
    requires Inv(s);
    requires Redirect(s.bcv, s'.bcv, redirect);
    ensures Acyclic(s');
    ensures G.IsAcyclic(s'.bcv.view);
  {
    RedirectResultingGraph(s, s', redirect);

    // find a reference reached from newly added references, ensures it was reachable from the old parent
    forall ref | ref in G.NewlyReachableReferences(s.bcv.view, s'.bcv.view, redirect.parentref)
      ensures ref in G.ReachableReferences(s.bcv.view, redirect.parentref)
    {
      var path :| G.NewPath(s.bcv.view, s'.bcv.view, redirect.parentref, path) && Last(path) == ref;

      if |path| == 2 {
        assert path[1] == ref;
        var key :| ChildMapsToRef(redirect.new_parent.children, key, ref);
        assert key !in redirect.keys;
        assert G.IsPath(s.bcv.view, [redirect.parentref, ref]) by { reveal_RedirectReads(); }
      } else {
        var _ := RedirectNewPathReachableFromOldPath(s, s', redirect, path, ref);
      }
    }

    forall path |
      && IsPath(s'.bcv.view, path)
      && (forall i :: 0 <= i < |path| ==> path[i] in s'.bcv.view.Keys - s.bcv.view.Keys)
    ensures !IsCycle(s'.bcv.view, path)
    {
      if (IsCycle(s'.bcv.view, path)) {
        RedirectOnlyPredOfChildIsParent(s, s', redirect, Last(path), path[0]);
        assert false by { reveal_RedirectReads(); }
        /*
        assert path[0] in redirect.new_children.Keys;
        assert Last(path) in redirect.new_children.Keys;
        assert path[0] in Successors(s'.bcv.view[Last(path)]);

        // TODO duplication with above
        var new_childref := Last(path);
        var new_child := s'.bcv.view[new_childref];
        var ref := path[0];
        assert new_childref in redirect.new_children;
        assert ref in redirect.new_children[new_childref].children.Values;
        var key :| IMapsTo(redirect.new_parent.children, key, new_childref) && IMapsTo(new_child.children, key, ref) && key in redirect.keys && key in redirect.old_parent.children;
        var old_childref := redirect.old_parent.children[key];
        var i :| 0 <= i < |redirect.old_childrefs| && redirect.old_childrefs[i] == old_childref;
        assert BI.ReadStep(s.bcv, RedirectReads(redirect)[i+1]);

        assert path[0] in s.bcv.view;
        assert false;
        */
      }
    }

    G.LocalEditPreservesAcyclic(s.bcv.view, s'.bcv.view, redirect.parentref); // observe
    AcyclicGraphImpliesAcyclic(s'); // observe
  }

  lemma RedirectPreservesRootHasNoPred(s: Variables, s': Variables, redirect: Redirect)
    requires Inv(s);
    requires Redirect(s.bcv, s'.bcv, redirect);
    ensures BI.RootHasNoPredecessor(s'.bcv.view)
  {
    forall ref | ref in s'.bcv.view
    ensures G.Root() !in G.Successors(s'.bcv.view[ref])
    {
      RedirectResultingGraph(s, s', redirect);
      if ref == redirect.parentref {
        assert G.Root() !in G.Successors(s'.bcv.view[ref]) by {
          reveal_RedirectReads();
        }
      } else if ref in redirect.old_childrefs {
        var i :| 0 <= i < |redirect.old_childrefs| && redirect.old_childrefs[i] == ref;
        assert BI.ReadStep(s.bcv, RedirectReads(redirect)[i+1]);
        assert ref in s.bcv.view by {
          reveal_RedirectReads();
        }
        assert G.Root() !in G.Successors(s'.bcv.view[ref]);
      } else if ref in redirect.new_childrefs {
        if G.Root() in G.Successors(s'.bcv.view[ref]) {
          var edge :| edge in s'.bcv.view[ref].children.Values && edge.ref == G.Root();
          assert edge in redirect.new_children[ref].children.Values;
          var key := ValidRedirectNewGrandchildrenGetKey(redirect, ref, edge);
          var old_childref := redirect.old_parent.children[key].ref;
          
          RedirectOldChildInView(s, s', redirect, old_childref);
          assert ref in Successors(s.bcv.view[old_childref]);
          assert ref in s.bcv.view;
          assert false;
        }
      } else {
        assert ref !in redirect.new_children.Keys;
        assert G.Root() !in G.Successors(s'.bcv.view[ref]);
      }
    }
  }

  lemma ClonePreservesAcyclic(s: Variables, s': Variables, clone: Clone)
    requires Inv(s)
    requires Clone(s.bcv, s'.bcv, clone)
    ensures G.IsAcyclic(s'.bcv.view)
    ensures Acyclic(s')
  {
    forall ref | ref in G.NewlyReachableReferences(s.bcv.view, s'.bcv.view, Root())
      ensures ref in G.ReachableReferences(s.bcv.view, Root())
    {
      var path :| G.NewPath(s.bcv.view, s'.bcv.view, Root(), path) && Last(path) == ref;
      if path[1] == ref { // path reached directly from root
        var key :| key in clone.newroot.children && clone.newroot.children[key].ref == ref;
        if key in clone.new_to_old {} // observe
        assert G.IsPath(s.bcv.view, [Root(), ref]);
      } else {} // ref reached from non root nodes, no changes made
      assert ref in G.ReachableReferences(s.bcv.view, Root());
     }
    G.LocalEditPreservesAcyclic(s.bcv.view, s'.bcv.view, Root());
    AcyclicGraphImpliesAcyclic(s');
  }

  lemma ClonePreservesRootHasNoPred(s: Variables, s': Variables, clone: Clone)
    requires Inv(s)
    requires Clone(s.bcv, s'.bcv, clone);
    ensures BI.RootHasNoPredecessor(s'.bcv.view)
  {
    forall ref | ref in s'.bcv.view
    ensures G.Root() !in G.Successors(s'.bcv.view[ref])
    {
      if ref == G.Root() && G.Root() in G.Successors(s'.bcv.view[ref]) {
        var key :| (
          && key in clone.new_to_old
          && ChildMapsToRef(clone.newroot.children, key, G.Root()));
        assert clone.newroot.children[key] == clone.oldroot.children[clone.new_to_old[key]];
      }
    }
  }

  //
  // Preservation proofs
  //

  lemma LookupAfterFirstHasNoRoot(s: Variables, lookup: Lookup)
  requires Inv(s)
  requires IsPathLookup(s.bcv.view, lookup)
  ensures forall i | 1 <= i < |lookup| :: lookup[i].readOp.ref != Root()
  {
    forall i | 1 <= i < |lookup|
    ensures lookup[i].readOp.ref != Root()
    {
      assert LookupFollowsChildRefAtLayer(lookup, i-1);
    }
  }

  lemma GrowPreservesLookups(s: Variables, s': Variables, start: Reference, growth: RootGrowth)
  requires Inv(s)
  requires Grow(s.bcv, s'.bcv, growth)
  ensures PreservesLookups(s, s', start)
  {
    forall lookup:Lookup, key, value | IsSatisfyingLookupFrom(s.bcv.view, key, value, lookup, start)
    ensures exists lookup':Lookup :: IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start)
    {
      if start == Root() {
        // Add one for the new root
        var rootref := Root();

        var newroot := s'.bcv.view[rootref];

        //assert LookupIsAcyclic(lookup);
        var lookup' := [
          Layer(ReadOp(rootref, newroot), key),
          Layer(ReadOp(growth.newchildref, growth.oldroot), key)
        ] + lookup[1..];

        InterpretLookupAdditive([Layer(ReadOp(rootref, newroot), key), 
          Layer(ReadOp(growth.newchildref, growth.oldroot), key) ], lookup[1..]);
        InterpretLookupAdditive([lookup[0]], lookup[1..]);
        assert [lookup[0]] + lookup[1..] == lookup;

        forall i | 0 <= i < |lookup'|-1
        ensures LookupFollowsChildRefAtLayer(lookup', i)
        ensures LookupFollowsEdgeAtLayer(lookup', i)
        {
          if i == 0 {
          } else {
            assert LookupFollowsChildRefAtLayer(lookup, i-1);
            assert LookupFollowsEdgeAtLayer(lookup, i-1);
          }
        }

        assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start);
      } else {
        LookupAfterFirstHasNoRoot(s, lookup);
        assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup, start);
      }
    }
  }

  ////////
  //////// Flush
  ////////

  lemma PropagateInterperetation(lookup:Lookup, lookup':Lookup, i:int, middle:Lookup, middle':Lookup, key:Key)
    requires 0 <= i < |lookup|-1
    requires |lookup'| == |lookup|
    requires lookup[..i] == lookup'[..i]
    requires lookup[i+2..] == lookup'[i+2..]
    requires lookup == lookup[..i] + middle + lookup[i+2..]
    requires lookup' == lookup'[..i] + middle' + lookup'[i+2..]
    requires LookupVisitsWFNodes(lookup)
    requires LookupVisitsWFNodes(middle)
    requires LookupVisitsWFNodes(middle')
    requires InterpretLookup(middle) == InterpretLookup(middle')
    ensures LookupVisitsWFNodes(lookup')
    ensures InterpretLookup(lookup) == InterpretLookup(lookup')
  {
    InterpretLookupAdditive3(lookup[..i], middle, lookup[i+2..]);
    InterpretLookupAdditive3(lookup'[..i], middle', lookup'[i+2..]);
  }

  lemma {:timeLimitMultiplier 4} FlushMovedKeysSameLookup(s: Variables, s': Variables, start: Reference, 
    flush:NodeFlush, lookup: Lookup, parentLayer: int, key: Key, value: Value)
  returns (lookup': Lookup)
  requires Inv(s)
  requires Flush(s.bcv, s'.bcv, flush)
  requires IsSatisfyingLookupFrom(s.bcv.view, key, value, lookup, start)
  requires 0 <= parentLayer < |lookup| && lookup[parentLayer].readOp.ref == flush.parentref
  requires lookup[parentLayer].currentKey in flush.movedkeys
  ensures IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start)
  {
    assume false;
    var parentkey := lookup[parentLayer].currentKey;
    if |lookup| - 1 == parentLayer { // we stopped at f.parent
      lookup' := lookup[..parentLayer] + [ Layer(ReadOp(flush.parentref, flush.newparent),parentkey) ]
          + [ Layer(ReadOp(flush.newchildref, flush.newchild), parentkey) ];

      forall j | 0 <= j < |lookup'|
        ensures IMapsTo(s'.bcv.view, lookup'[j].readOp.ref, lookup'[j].readOp.node) {}

      forall j | 0 <= j < |lookup'|-1
        ensures LookupFollowsChildRefAtLayer(lookup', j)
        ensures LookupFollowsEdgeAtLayer(lookup', j)
      {
        if j <= parentLayer-1 {
          assert LookupFollowsChildRefAtLayer(lookup, j);
          assert LookupFollowsEdgeAtLayer(lookup, j);
        }
      }
      assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start); // observe
    } else {
      reveal_ValidRedirect(); // some redirect property is needed here

      var middle := [ lookup[parentLayer] ] + [ lookup[parentLayer+1] ];
      var middle' := ([ Layer(ReadOp(flush.parentref, flush.newparent), parentkey) ] 
          + [ Layer(ReadOp(flush.newchildref, flush.newchild), parentkey) ]);

      assert lookup == lookup[..parentLayer] + middle + lookup[parentLayer+2..];
      lookup' := lookup[..parentLayer] + middle' + lookup[parentLayer+2..];

      forall j | 0 <= j < |lookup'|
      ensures IMapsTo(s'.bcv.view, lookup'[j].readOp.ref, lookup'[j].readOp.node) { }

      assert lookup[..parentLayer] == lookup'[..parentLayer];
      assert lookup[parentLayer+2..] == lookup'[parentLayer+2..];
      assert LookupFollowsChildRefAtLayer(lookup, parentLayer); // Handles the j==parentLayer+1 case; connects middle[1] to f.child.
      assert LookupFollowsEdgeAtLayer(lookup, parentLayer);

      forall j | 0 <= j < |lookup'|-1
        ensures LookupFollowsChildRefAtLayer(lookup', j)
        ensures LookupFollowsEdgeAtLayer(lookup', j)
      {
        assert LookupFollowsChildRefAtLayer(lookup, j);
        assert LookupFollowsEdgeAtLayer(lookup, j);
      }            

      if (parentkey in flush.flushedkeys) {
        assert InterpretLookup([lookup'[parentLayer]]) == G.M.Update(G.M.NopDelta());
        assert InterpretLookup(middle) == InterpretLookup(middle');
      } else {
        assert InterpretLookup(middle) == InterpretLookup(middle');
      }
      PropagateInterperetation(lookup, lookup', parentLayer, middle, middle', parentkey);
      assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start); // observe
    }
  }

  lemma FlushPreservesLookups(s: Variables, s': Variables, start: Reference, flush:NodeFlush)
  requires Inv(s)
  requires Flush(s.bcv, s'.bcv, flush)
  ensures PreservesLookups(s, s', start)
  {
    var f := flush;
    var newchild := f.newchild;
    var newparent := f.newparent;

    forall lookup:Lookup, key, value | IsSatisfyingLookupFrom(s.bcv.view, key, value, lookup, start)
      ensures exists lookup':Lookup :: IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start)
    {
      // for the constructed lookup, only need to prove the ones where lookup goes through the flushed parent ref
      if parentLayer :| 0 <= parentLayer < |lookup| && lookup[parentLayer].readOp.ref == f.parentref {
        var parentkey := lookup[parentLayer].currentKey;
        if parentkey !in f.movedkeys {
          // looking at parentref unmoved keys preserve the same lookup as before 
          var lookup' := lookup[parentLayer := Layer(ReadOp(f.parentref, newparent), parentkey)];
          forall j | 0 <= j < |lookup'|
            ensures IMapsTo(s'.bcv.view, lookup'[j].readOp.ref, lookup'[j].readOp.node) { }
          assert lookup[..parentLayer] + [lookup[parentLayer]] + lookup[parentLayer+1..] == lookup; // observe
          assert lookup'[..parentLayer] + [lookup'[parentLayer]] + lookup'[parentLayer+1..] == lookup'; // observe
          InterpretLookupAdditive3(lookup[..parentLayer], [lookup[parentLayer]], lookup[parentLayer+1..]);
          InterpretLookupAdditive3(lookup'[..parentLayer], [lookup'[parentLayer]], lookup'[parentLayer+1..]);

          forall j | 0 <= j < |lookup'|-1
            ensures LookupFollowsChildRefAtLayer(lookup', j)
            ensures LookupFollowsEdgeAtLayer(lookup', j)
          {
            assert LookupFollowsChildRefAtLayer(lookup, j); // observe
            assert LookupFollowsEdgeAtLayer(lookup, j); // observe
          }
          assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start); // observe
        } else {
          var _:= FlushMovedKeysSameLookup(s, s', start, flush, lookup, parentLayer, key, value);
        }
      } else {
        assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup, start);
      }
    }
  }

  ////////
  //////// Redirect
  ////////

  lemma RedirectUnmovedKeysSameLookup(s: Variables, s': Variables, start: Reference, redirect: Redirect, 
    lookup: Lookup, parentLayer: int, key: Key, value: Value)
  returns (lookup': Lookup)
  requires Inv(s)
  requires Redirect(s.bcv, s'.bcv, redirect)
  requires IsSatisfyingLookupFrom(s.bcv.view, key, value, lookup, start)
  requires 0 <= parentLayer < |lookup| && lookup[parentLayer].readOp.ref == redirect.parentref
  requires lookup[parentLayer].currentKey !in redirect.keys || parentLayer == |lookup| - 1 
  ensures IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start)
  {
    var parentkey := lookup[parentLayer].currentKey;
    lookup' := lookup[parentLayer := Layer(G.ReadOp(redirect.parentref, redirect.new_parent), parentkey)];
    
    RedirectParentInViews(s, s', redirect);

    forall j | 0 <= j < |lookup'|-1
    ensures LookupFollowsChildRefAtLayer(lookup', j)
    ensures LookupFollowsEdgeAtLayer(lookup', j)
    {
      assert LookupFollowsChildRefAtLayer(lookup, j);
      assert LookupFollowsEdgeAtLayer(lookup, j);
    }

    InterpretLookupAdditive3(lookup'[..parentLayer], [lookup'[parentLayer]], lookup'[parentLayer+1..]);
    assert lookup' == lookup'[..parentLayer] + [lookup'[parentLayer]] + lookup'[parentLayer+1..];
          
    InterpretLookupAdditive3(lookup[..parentLayer], [lookup[parentLayer]], lookup[parentLayer+1..]);
    assert lookup == lookup[..parentLayer] + [lookup[parentLayer]] + lookup[parentLayer+1..];
          
    RedirectResultingGraph(s, s', redirect);
    assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start);
  }

  lemma {:timeLimitMultiplier 4} RedirectPreservesLookups(s: Variables, s': Variables, start: Reference, redirect: Redirect)
    requires Inv(s)
    requires Redirect(s.bcv, s'.bcv, redirect)
    ensures PreservesLookups(s, s', start)
  {
    RedirectParentInViews(s, s', redirect);

    forall lookup:Lookup, key, value | IsSatisfyingLookupFrom(s.bcv.view, key, value, lookup, start)
      ensures exists lookup':Lookup :: IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start)
    {
      if i :| 0 <= i < |lookup| && lookup[i].readOp.ref == redirect.parentref {
        var parentkey := lookup[i].currentKey;
        if parentkey in redirect.keys && i < |lookup| - 1 { // parent not leaf for parentkey
          var new_childref := redirect.new_parent.children[parentkey].ref;
          var new_child := redirect.new_children[new_childref];
          var old_childref := redirect.old_parent.children[parentkey].ref;
          var old_child := redirect.old_children[old_childref];

          RedirectOldChildInView(s, s', redirect, old_childref);
          assert LookupFollowsChildRefAtLayer(lookup, i);
          assert lookup[i+1].readOp.ref == old_childref;
          assert lookup[i+1].readOp.node == old_child;

          var lookup' := lookup[i := Layer(G.ReadOp(redirect.parentref, redirect.new_parent), parentkey)]
            [i+1 := Layer(G.ReadOp(new_childref, new_child), parentkey)];

          forall j | 0 <= j < |lookup'|-1
            ensures LookupFollowsChildRefAtLayer(lookup', j)
            ensures LookupFollowsEdgeAtLayer(lookup', j)
          {
            if j == i {
            } else if j == i + 1 {
              assert LookupFollowsChildRefAtLayer(lookup, i);
              assert LookupFollowsEdgeAtLayer(lookup, i);              
              assert LookupFollowsChildRefAtLayer(lookup, i+1);
              assert LookupFollowsEdgeAtLayer(lookup, i+1);
            } else {
              assert LookupFollowsChildRefAtLayer(lookup, j);
              assert LookupFollowsEdgeAtLayer(lookup, j);
            }
          }

          var middle :=  [lookup[i]]  + [lookup[i+1]];
          var middle' := [lookup'[i]] + [lookup'[i+1]];

          assert lookup[i].readOp.node.buffer == lookup'[i].readOp.node.buffer;
          assert LookupFollowsChildRefAtLayer(lookup, i);
          assert LookupFollowsEdgeAtLayer(lookup, i);
          assert InterpretLookup(middle') == InterpretLookup(middle);

          PropagateInterperetation(lookup, lookup', i, middle, middle', parentkey);
          assert lookup' == lookup'[..i] + middle' + lookup'[i+2..];
          assert middle == lookup[i..i+2];
          assert lookup == lookup[..i] + middle + lookup[i+2..];
          RedirectResultingGraph(s, s', redirect);
          assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start);
        } else {
          var _ := RedirectUnmovedKeysSameLookup(s, s', start, redirect, lookup, i, key, value);
        }
      } else {
        RedirectResultingGraph(s, s', redirect);
        assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup, start);
      }
    }
  }

  ////////
  //////// Clone
  ////////

  predicate CloneKeysEqualOldKeys(s: Variables, s': Variables, clone: Clone)
  {
    && (forall  key | key in clone.new_to_old :: KeyHasSatisfyingLookup(s.bcv.view, clone.new_to_old[key], Root()))
    && (forall lookup, key1, value | key1 in clone.new_to_old && IsSatisfyingLookupFrom(s.bcv.view, clone.new_to_old[key1], value, lookup, Root())
      :: exists lookup' :: IsSatisfyingLookupFrom(s'.bcv.view, key1, value, lookup', Root()))
  }

  // lemma used by implies invariants 
  lemma {:timeLimitMultiplier 4} ClonePreservesLookups(s: Variables, s': Variables, clone: Clone)
    requires Inv(s)
    requires Clone(s.bcv, s'.bcv, clone)
    ensures CloneKeysEqualOldKeys(s, s', clone)
    ensures PreservesLookupsExceptRange(s, s', clone.new_to_old.Keys)
  {
    // keys that are not cloned remain the same
    forall lookup, key, value | key !in clone.new_to_old && IsSatisfyingLookupFrom(s.bcv.view, key, value, lookup, Root())
      ensures exists lookup' :: IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', Root())
    {
      var lookup' := lookup[ 0:= Layer(G.ReadOp(Root(), clone.newroot), key)];
      InterpsEqualIfAllBuffersEqual(lookup, lookup');

      forall idx | ValidLayerIndex(lookup', idx) && idx < |lookup'| - 1
      ensures LookupFollowsChildRefAtLayer(lookup', idx)
      ensures LookupFollowsEdgeAtLayer(lookup', idx)
      {
        assert LookupFollowsChildRefAtLayer(lookup, idx);
        assert LookupFollowsEdgeAtLayer(lookup, idx);
      }
      assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', Root());
    }
    assert PreservesLookupsExceptRange(s, s', clone.new_to_old.Keys);

    // keys that are cloned
    // first show clone is closed
    assert (forall  key | key in clone.new_to_old :: KeyHasSatisfyingLookup(s.bcv.view, clone.new_to_old[key], Root())); // observe

    // then show every cloned key is equivalent to a lookup path in the old view
    forall lookup, key1, value | key1 in clone.new_to_old 
      && IsSatisfyingLookupFrom(s.bcv.view, clone.new_to_old[key1], value, lookup, Root())
      ensures exists lookup' :: IsSatisfyingLookupFrom(s'.bcv.view, key1, value, lookup', Root())
    {
      var lookup' : seq<Layer> := lookup[ 0:= Layer(G.ReadOp(Root(), clone.newroot), key1)];
      InterpsEqualIfAllBuffersEqual(lookup, lookup');
      
      forall idx | ValidLayerIndex(lookup', idx) && idx < |lookup'| - 1
      ensures LookupFollowsChildRefAtLayer(lookup', idx)
      ensures LookupFollowsEdgeAtLayer(lookup', idx)
      {
        assert LookupFollowsChildRefAtLayer(lookup, idx);
        assert LookupFollowsEdgeAtLayer(lookup, idx);
      }
      assert IMapsTo(s'.bcv.view, Root(), clone.newroot); // observe
      assert IsSatisfyingLookupFrom(s'.bcv.view, key1, value, lookup', Root()); // observe
    }
  }

  ////////
  //////// Invariant proofs
  ////////

  lemma InitImpliesInv(s: Variables)
    requires Init(s)
    ensures Inv(s)
  {
    forall key | MS.InDomain(key)
    ensures IsSatisfyingLookupFrom(s.bcv.view, key, G.M.DefaultValue(), [Layer(ReadOp(Root(), EmptyNode()), key)], Root())
    {
    }
    forall lookup:Lookup | IsPathLookup(s.bcv.view, lookup)
    ensures LookupIsAcyclic(lookup)
    {
      assert lookup[0].readOp.ref == Root();
      forall i, j | 0 <= i < |lookup| && 0 <= j < |lookup| && i != j
      ensures lookup[i].readOp.ref != lookup[j].readOp.ref
      {
        assert LookupFollowsChildRefAtLayer(lookup, 0);
      }
    }
  }

  lemma QueryStepPreservesInvariant(s: Variables, s': Variables)
    requires Inv(s)
    requires BI.OpTransaction(s.bcv, s'.bcv, [])
    ensures Inv(s')
  {
  }

  lemma InsertMessagePreservesAcyclicAndReachablePointersValid(s: Variables, s': Variables, ins: MessageInsertion)
    requires Inv(s)
    requires InsertMessage(s.bcv, s'.bcv, ins)
    ensures G.IsAcyclic(s'.bcv.view)
    ensures Acyclic(s')
  {
    G.LocalEditPreservesAcyclic(s.bcv.view, s'.bcv.view, G.Root());
    AcyclicGraphImpliesAcyclic(s');
  }

  lemma InsertMessagePreservesLookupsPut(s: Variables, s': Variables, ins: MessageInsertion)
    requires Inv(s)
    requires InsertMessage(s.bcv, s'.bcv, ins)
    requires ins.msg.Define?
    ensures PreservesLookupsPut(s, s', ins.key, ins.msg.value);
  {
    forall lookup:Lookup, key1, value | key1 != ins.key && IsSatisfyingLookupFrom(s.bcv.view, key1, value, lookup, Root())
      ensures exists lookup':Lookup :: IsSatisfyingLookupFrom(s'.bcv.view, key1, value, lookup', Root())
    {
      // take in a seq of layer and convert to another seq of layer
      var lookup' := Apply((x: Layer) => Layer(G.ReadOp(x.readOp.ref, if x.readOp.ref in s'.bcv.view then s'.bcv.view[x.readOp.ref] else EmptyNode()), x.currentKey), lookup);
      InterpsEqualIfAllBuffersEqual(lookup, lookup');

      assert BufferDefinesValue(InterpretLookup(lookup'), value);

      forall idx | ValidLayerIndex(lookup', idx) && idx < |lookup'| - 1
      ensures LookupFollowsChildRefAtLayer(lookup', idx)
      ensures LookupFollowsEdgeAtLayer(lookup', idx)
      {
        assert LookupFollowsChildRefAtLayer(lookup, idx);
        assert LookupFollowsEdgeAtLayer(lookup, idx);
      }

      assert IsSatisfyingLookupFrom(s'.bcv.view, key1, value, lookup', Root());
    }

    {
      assert KeyHasSatisfyingLookup(s.bcv.view, ins.key, Root());
      var value, lookup: Lookup :| IsSatisfyingLookupFrom(s.bcv.view, ins.key, value, lookup, Root());
      var lookup' := Apply((x: Layer) => Layer(G.ReadOp(x.readOp.ref, if x.readOp.ref in s'.bcv.view then s'.bcv.view[x.readOp.ref] else EmptyNode()), x.currentKey), lookup);

      assert lookup' == [lookup'[0]] + lookup'[1..];
      InterpretLookupAdditive([lookup'[0]], lookup'[1..]);
      assert lookup[1..] == lookup'[1..];
      G.M.MergeIsAssociative(ins.msg, InterpretLookup([lookup[0]]), InterpretLookup(lookup[1..]));
      InterpretLookupAdditive([lookup[0]], lookup[1..]);
      assert lookup == [lookup[0]] + lookup[1..];
      var message' := G.M.Merge(ins.msg, InterpretLookup(lookup));

      forall idx | ValidLayerIndex(lookup', idx) && idx < |lookup'| - 1
      // ensures key in lookup'[idx].readOp.node.children
      ensures LookupFollowsChildRefAtLayer(lookup', idx)
      ensures LookupFollowsEdgeAtLayer(lookup', idx)
      {
        assert LookupFollowsChildRefAtLayer(lookup, idx);
        assert LookupFollowsEdgeAtLayer(lookup, idx);
      }

      assert IsSatisfyingLookupFrom(s'.bcv.view, ins.key, message'.value, lookup', Root());
    }
  }

  lemma InsertMessagePreservesNonrootLookups(s: Variables, s': Variables, key: Key, msg: BufferEntry, oldroot: Node, start: Reference)
    requires Inv(s)
    requires InsertMessage(s.bcv, s'.bcv, MessageInsertion(key, msg, oldroot))
    requires start != Root()
    ensures PreservesLookups(s, s', start)
  {
    forall lookup:Lookup, key, value | IsSatisfyingLookupFrom(s.bcv.view, key, value, lookup, start)
    ensures exists lookup':Lookup :: IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start)
    {
      LookupAfterFirstHasNoRoot(s, lookup);
      var lookup' := lookup;
      assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start);
    }
  }

  lemma ClonePreservesNonrootLookups(s: Variables, s': Variables, start: Reference, clone: Clone)
    requires Inv(s)
    requires Clone(s.bcv, s'.bcv, clone)
    requires start != Root()
    ensures PreservesLookups(s, s', start)
  {
    forall lookup:Lookup, key, value | IsSatisfyingLookupFrom(s.bcv.view, key, value, lookup, start)
    ensures exists lookup':Lookup :: IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start)
    {
      LookupAfterFirstHasNoRoot(s, lookup);
      var lookup' := lookup;
      assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start);
    }
  }

  lemma InsertMessageStepPreservesInvariant(s: Variables, s': Variables, ins: MessageInsertion)
    requires Inv(s)
    requires InsertMessage(s.bcv, s'.bcv, ins)
    // We can have this msg.Define? condition becasue right now the uiop condition
    // enforces that the inserted message must be a Define. Eventually we'll need
    // to expand the semantics of the map and the proof to support non-Define messages.
    requires ins.msg.Define?
    ensures Inv(s')
  {
    InsertMessagePreservesAcyclicAndReachablePointersValid(s, s', ins);
    InsertMessagePreservesLookupsPut(s, s', ins);
  }

  lemma FlushStepPreservesInvariant(s: Variables, s': Variables, flush: NodeFlush)
    requires Inv(s)
    requires Flush(s.bcv, s'.bcv, flush)
    ensures Inv(s')
  {
    FlushPreservesAcyclic(s, s', flush);
    FlushPreservesLookups(s, s', Root(), flush);
    FlushPreservesRootHasNoPred(s, s', flush);
  }

  lemma GrowStepPreservesInvariant(s: Variables, s': Variables, growth: RootGrowth)
    requires Inv(s)
    requires Grow(s.bcv, s'.bcv, growth)
    ensures Inv(s')
  {
    GrowPreservesAcyclic(s, s', growth);
    GrowPreservesLookups(s, s', Root(), growth);
  }
 
  // Redirect
  lemma RedirectStepPreservesInvariant(s: Variables, s': Variables, redirect: Redirect)
    requires Inv(s)
    requires Redirect(s.bcv, s'.bcv, redirect)
    ensures Inv(s')
  {
    RedirectPreservesAcyclic(s, s', redirect);
    RedirectPreservesLookups(s, s', Root(), redirect);
    BI.TransactionPreservesInv(s.bcv, s'.bcv, RedirectOps(redirect));
    RedirectPreservesRootHasNoPred(s, s', redirect);
  }

  // Clone
  lemma CloneStepPreservesInvariant(s: Variables, s': Variables, clone: Clone)
    requires Inv(s)
    requires Clone(s.bcv, s'.bcv, clone)
    ensures Inv(s')
  {
    ClonePreservesAcyclic(s, s', clone);
    ClonePreservesLookups(s, s', clone);
    ClonePreservesRootHasNoPred(s, s', clone);
  }

  // GC Step
  lemma GCStepPreservesIsPathLookup(s: Variables, s': Variables, refs: iset<Reference>, lookup: Lookup)
    requires Inv(s)
    requires BI.GC(s.bcv, s'.bcv, refs)
    requires IsPathLookup(s.bcv.view, lookup);
    requires lookup[0].readOp.ref !in refs
    ensures IsPathLookup(s'.bcv.view, lookup);
  {
    if |lookup| == 1 {
    } else {
      var lookup' := DropLast(lookup);
      forall idx | 0 <= idx < |lookup'| - 1
      ensures LookupFollowsChildRefAtLayer(lookup', idx)
      ensures LookupFollowsEdgeAtLayer(lookup', idx)
      {
        assert LookupFollowsChildRefAtLayer(lookup, idx);
        assert LookupFollowsEdgeAtLayer(lookup, idx);
      }
      GCStepPreservesIsPathLookup(s, s', refs, lookup');
      assert LookupFollowsChildRefAtLayer(lookup, |lookup| - 2);
    }
  }

  lemma GCStepPreservesAcyclicity(s: Variables, s': Variables, refs: iset<Reference>)
    requires Inv(s)
    requires BI.GC(s.bcv, s'.bcv, refs)
    ensures G.IsAcyclic(s'.bcv.view)
    ensures Acyclic(s')
  {
    G.UnallocPreservesAcyclic(s.bcv.view, s'.bcv.view);
    AcyclicGraphImpliesAcyclic(s');
  }

  lemma GCStepPreservesLookups(s: Variables, s': Variables, start: Reference, refs: iset<Reference>)
    requires Inv(s)
    requires BI.GC(s.bcv, s'.bcv, refs)
    requires start !in refs
    ensures PreservesLookups(s, s', start)
  {
    forall lookup:Lookup, key, value | IsSatisfyingLookupFrom(s.bcv.view, key, value, lookup, start)
    ensures exists lookup':Lookup :: IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start)
    {
      GCStepPreservesIsPathLookup(s, s', refs, lookup);
      assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup, start);
    }
  }

  lemma GCStepPreservesInvariant(s: Variables, s': Variables, refs: iset<Reference>)
    requires Inv(s)
    requires BI.GC(s.bcv, s'.bcv, refs)
    ensures Inv(s')
  {
    BI.GCPreservesInv(s.bcv, s'.bcv, refs);
    GCStepPreservesAcyclicity(s, s', refs);
    GCStepPreservesLookups(s, s', Root(), refs);
  }

  // Putting it all together

  lemma BetreeStepPreservesInvariant(s: Variables, s': Variables, uiop: UI.Op, betreeStep: BetreeStep)
    requires Inv(s)
    requires Betree(s, s', uiop, betreeStep)
    ensures Inv(s')
  {
    match betreeStep {
      case BetreeQuery(q) => QueryStepPreservesInvariant(s, s');
      case BetreeSuccQuery(sq) => QueryStepPreservesInvariant(s, s');
      case BetreeInsert(ins) => InsertMessageStepPreservesInvariant(s, s', ins);
      case BetreeFlush(flush) => FlushStepPreservesInvariant(s, s', flush);
      case BetreeGrow(growth) => GrowStepPreservesInvariant(s, s', growth);
      case BetreeRedirect(redirect) => RedirectStepPreservesInvariant(s, s', redirect);
      case BetreeClone(clone) => CloneStepPreservesInvariant(s, s', clone);
    }
  }

  lemma NextStepPreservesInvariant(s: Variables, s': Variables, uiop: UI.Op, step: Step)
    requires Inv(s)
    requires NextStep(s, s', uiop, step)
    ensures Inv(s')
  {
    match step {
      case GCStep(refs) => GCStepPreservesInvariant(s, s', refs);
      case BetreeStep(betreeStep) => BetreeStepPreservesInvariant(s, s', uiop, betreeStep);
      case StutterStep => {}
    }
  }
  
  lemma NextPreservesInv(s: Variables, s': Variables, uiop: UI.Op)
    requires Inv(s)
    requires Next(s, s', uiop)
    ensures Inv(s')
  {
    var step :| NextStep(s, s', uiop, step);
    NextStepPreservesInvariant(s, s', uiop, step);
  }
}
