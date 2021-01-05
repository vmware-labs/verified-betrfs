include "../lib/Base/Maps.i.dfy"
include "../lib/Base/sequences.i.dfy"
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
    forall i :: 0 <= i < |lookup| ==> IMapsTo(view, lookup[i].ref, lookup[i].node)
  }

  predicate IsPathLookup(view: BI.View, key: UKey, lookup: Lookup) {
    && |lookup| > 0
    && LookupRespectsView(view, lookup)
    && LookupFollowsChildRefs(key, lookup)
  }

  predicate IsSatisfyingLookup(view: BI.View, key: UKey, value: Value, lookup: Lookup) {
    && IsPathLookup(view, key, lookup)
    && LookupVisitsWFNodes(lookup)
    && BufferDefinesValue(InterpretLookup(lookup, key), value)
  }

  predicate IsSatisfyingLookupFrom(view: BI.View, key: UKey, value: Value, lookup: Lookup, start: Reference) {
    && IsSatisfyingLookup(view, key, value, lookup)
    && lookup[0].ref == start
  }

  predicate KeyHasSatisfyingLookup(view: BI.View, key: UKey, start: Reference)
  {
    exists lookup: Lookup, value ::
      && IsSatisfyingLookupFrom(view, key, value, lookup, start)
  }

  function PathOfLookup(lookup: Lookup) : (path : G.Path)
    ensures |path| == |lookup|
    ensures forall i :: 0 <= i < |path| ==> path[i] == lookup[i].ref
  {
    if lookup == [] then []
    else PathOfLookup(DropLast(lookup)) + [Last(lookup).ref]
  }
  
  predicate LookupIsAcyclic(lookup: Lookup) {
    forall i, j :: 0 <= i < |lookup| && 0 <= j < |lookup| && i != j ==> lookup[i].ref != lookup[j].ref
  }

  predicate Acyclic(s: Variables) {
    forall key, lookup ::
      IsPathLookup(s.bcv.view, key, lookup) ==>
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

  predicate PreservesLookupsExcept(s: Variables, s': Variables, start: Reference, exceptQuery: UKey)
  {
    forall lookup: Lookup, key, value :: key != exceptQuery && IsSatisfyingLookupFrom(s.bcv.view, key, value, lookup, start) ==>
      exists lookup': Lookup :: IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start)
  }

  // TODO generalize this to explain how the value changes when a non-Define
  // message is inserted
  predicate PreservesLookupsPut(s: Variables, s': Variables, key: UKey, value: Value)
  {
    && PreservesLookupsExcept(s, s', Root(), key)
    && exists lookup: Lookup :: IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup, Root())
  }

  //

  lemma InterpsEqualOfAllBuffersEqual(a: Lookup, b: Lookup, key: UKey)
  requires LookupVisitsWFNodes(a);
  requires LookupVisitsWFNodes(b);
  requires |a| == |b|
  requires forall j | 0 <= j < |a| :: a[j].node.buffer[key] == b[j].node.buffer[key]
  ensures InterpretLookup(a, key) == InterpretLookup(b, key)
  {
    if |a| == 0 {
    } else {
      InterpsEqualOfAllBuffersEqual(DropLast(a), DropLast(b), key);
    }
  }

  lemma InterpretLookupAdditive(a: Lookup, b: Lookup, key: UKey)
  requires LookupVisitsWFNodes(a);
  requires LookupVisitsWFNodes(b);
  ensures InterpretLookup(a + b, key) == G.M.Merge(InterpretLookup(a, key), InterpretLookup(b, key))
  {
    if |b| == 0 {
      assert a + b == a;
    } else {
      assert a + b == a + DropLast(b) + [Last(b)]; // observe
      assert forall l: Lookup :: |l| == 1 && LookupVisitsWFNodes(l) ==> InterpretLookup(l, key) == l[0].node.buffer[key]; // observe
      G.M.MergeIsAssociative(InterpretLookup(a, key), InterpretLookup(DropLast(b), key), InterpretLookup([Last(b)], key));
    }
  }

  lemma InterpretLookupAdditive3(a: Lookup, b: Lookup, c: Lookup, key: UKey)
  requires LookupVisitsWFNodes(a);
  requires LookupVisitsWFNodes(b);
  requires LookupVisitsWFNodes(c);
  ensures InterpretLookup(a + b + c, key) == G.M.Merge(G.M.Merge(InterpretLookup(a, key), InterpretLookup(b, key)), InterpretLookup(c, key))
  {
    InterpretLookupAdditive(a + b, c, key); // a + b
    InterpretLookupAdditive(a, b, key); // a + b
  }

  // CantEquivocate
  // It's a lemma here (follows from structure of Lookups) - not an invariant!

  lemma SatisfyingLookupsForKeyAgree(s: Variables, key: UKey, value: Value, value': Value, lookup: Lookup, lookup': Lookup, idx: int)
  requires IsSatisfyingLookup(s.bcv.view, key, value, lookup);
  requires IsSatisfyingLookup(s.bcv.view, key, value', lookup');
  requires 0 <= idx < |lookup|;
  requires 0 <= idx < |lookup'|;
  requires lookup[0].ref == lookup'[0].ref
  ensures lookup[idx] == lookup'[idx];
  {
    if (idx == 0) {
    } else {
      SatisfyingLookupsForKeyAgree(s, key, value, value', lookup, lookup', idx - 1);
      assert LookupFollowsChildRefAtLayer(key, lookup, idx-1);
      assert LookupFollowsChildRefAtLayer(key, lookup', idx-1);
    }
  }

  lemma CantEquivocateWlog(s: Variables, key: UKey, value: Value, value': Value, lookup: Lookup, lookup': Lookup)
  requires IsSatisfyingLookup(s.bcv.view, key, value, lookup);
  requires IsSatisfyingLookup(s.bcv.view, key, value', lookup');
  requires |lookup| <= |lookup'|
  requires lookup[0].ref == lookup'[0].ref
  ensures value == value';
  {

    var junk := lookup'[|lookup|..];
    forall idx | 0 <= idx < |lookup|
    ensures lookup'[idx] == lookup[idx];
    {
        SatisfyingLookupsForKeyAgree(s, key, value, value', lookup, lookup', idx);
    }
    assert lookup' == lookup + junk; // observe
    InterpretLookupAdditive(lookup, junk, key);
  }

  lemma CantEquivocate(s: Variables, key: UKey, value: Value, value': Value, lookup: Lookup, lookup': Lookup)
  requires IsSatisfyingLookup(s.bcv.view, key, value, lookup);
  requires IsSatisfyingLookup(s.bcv.view, key, value', lookup');
  requires lookup[0].ref == lookup'[0].ref
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

  predicate InsertMessage(s: BI.Variables, s': BI.Variables, key: UKey, msg: BufferEntry, oldroot: Node)
  {
    && ValidInsertion(MessageInsertion(key, msg, oldroot))
    && BI.Reads(s, InsertionReads(MessageInsertion(key, msg, oldroot)))
    && BI.OpTransaction(s, s', InsertionOps(MessageInsertion(key, msg, oldroot)))
  }

  predicate Flush(s: BI.Variables, s': BI.Variables, flush:NodeFlush)
  {
    && ValidFlush(flush)
    && BI.Reads(s, FlushReads(flush))
    && BI.OpTransaction(s, s', FlushOps(flush))
  }

  predicate Grow(s: BI.Variables, s': BI.Variables, oldroot: Node, newchildref: Reference)
  {
    && ValidGrow(RootGrowth(oldroot, newchildref))
    && BI.Reads(s, GrowReads(RootGrowth(oldroot, newchildref)))
    && BI.OpTransaction(s, s', GrowOps(RootGrowth(oldroot, newchildref)))
  }

  predicate Redirect(s: BI.Variables, s': BI.Variables, redirect: Redirect)
  {
    && ValidRedirect(redirect)
    && BI.Reads(s, RedirectReads(redirect))
    && BI.OpTransaction(s, s', RedirectOps(redirect))
  }

  predicate Query(s: BI.Variables, s': BI.Variables, key: UKey, value: Value, lookup: Lookup)
  {
    && ValidQuery(LookupQuery(key, value, lookup))
    && BI.Reads(s, QueryReads(LookupQuery(key, value, lookup)))
    && BI.OpTransaction(s, s', QueryOps(LookupQuery(key, value, lookup)))
  }

  predicate QueryDescent(s: BI.Variables, s': BI.Variables, redirect: Redirect)
  {
    && ValidRedirect(redirect)
    && BI.Reads(s, RedirectReads(redirect))
    && BI.OpTransaction(s, s', RedirectOps(redirect))
  }

  predicate SuccQuery(s: BI.Variables, s': BI.Variables, start: UI.RangeStart, results: seq<UI.SuccResult>, end: UI.RangeEnd, lookup: Lookup)
  {
    && ValidSuccQuery(BetreeSpec.SuccQuery(start, results, end, lookup))
    && BI.Reads(s, SuccQueryReads(BetreeSpec.SuccQuery(start, results, end, lookup)))
    && BI.OpTransaction(s, s', SuccQueryOps(BetreeSpec.SuccQuery(start, results, end, lookup)))
  }

  //
  // Acyclicity proofs
  //
  
  lemma AcyclicGraphImpliesAcyclic(s: Variables)
    requires IsAcyclic(s.bcv.view)
    ensures Acyclic(s)
  {
    var g := s.bcv.view;
    forall key, lookup: Lookup | IsPathLookup(s.bcv.view, key, lookup)
      ensures LookupIsAcyclic(lookup)
    {
      var path := PathOfLookup(lookup);
      forall i | 0 <= i < |path|-1
        ensures path[i] in g && path[i+1] in Successors(g[path[i]])
      {
        assert LookupFollowsChildRefAtLayer(key, lookup, i);
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
    forall ref | ref in G.NewlyReachableReferences(s.bcv.view, s'.bcv.view, f.parentref)
      ensures ref in G.ReachableReferences(s.bcv.view, f.parentref)
      {
        var path :| G.NewPath(s.bcv.view, s'.bcv.view, f.parentref, path) && Last(path) == ref;
        if path[1] == ref {
          assert G.IsPath(s.bcv.view, [f.parentref, ref]);
        } else {
          assert path[|path|-2] == f.newchildref;
          assert G.IsPath(s.bcv.view, [f.parentref, f.childref, ref]);
        }
      }
    G.LocalEditPreservesAcyclic(s.bcv.view, s'.bcv.view, f.parentref);
    AcyclicGraphImpliesAcyclic(s');
  }

  lemma GrowPreservesAcyclic(s: Variables, s': Variables, oldroot: Node, newchildref: Reference)
    requires Inv(s)
    requires Grow(s.bcv, s'.bcv, oldroot, newchildref)
    ensures G.IsAcyclic(s'.bcv.view)
    ensures Acyclic(s')
  {
    forall ref | ref in G.NewlyReachableReferences(s.bcv.view, s'.bcv.view, Root())
      ensures ref in G.ReachableReferences(s.bcv.view, Root())
    {
      var path :| G.NewPath(s.bcv.view, s'.bcv.view, Root(), path) && Last(path) == ref;
      assert path[|path|-2] == newchildref;
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
    var ops := RedirectOps(redirect);
    var smid := BI.GetPenultimateState(s.bcv, s'.bcv, ops);
    RedirectResultingGraphAfterAllocs(s.bcv, smid, redirect.new_childrefs, redirect.new_children);
    assert s'.bcv.view.Keys == smid.view.Keys;
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

      var new_childref := parentref;
      var new_child := s'.bcv.view[new_childref];
      assert new_childref in redirect.new_children;
      assert ref in redirect.new_children[new_childref].children.Values;
      var key :| IMapsTo(redirect.new_parent.children, key, new_childref) && IMapsTo(new_child.children, key, ref) && key in redirect.keys && key in redirect.old_parent.children;
      var old_childref := redirect.old_parent.children[key];
      var i :| 0 <= i < |redirect.old_childrefs| && redirect.old_childrefs[i] == old_childref;
      assert BI.ReadStep(s.bcv, RedirectReads(redirect)[i+1]);

      assert ref in s.bcv.view;
      assert false;
    } else {
      assert false;
    }
  }

  lemma RedirectPreservesAcyclic(s: Variables, s': Variables, redirect: Redirect)
    requires Inv(s);
    requires Redirect(s.bcv, s'.bcv, redirect);
    ensures Acyclic(s');
    ensures G.IsAcyclic(s'.bcv.view);
  {
    RedirectResultingGraph(s, s', redirect);

    forall ref | ref in G.NewlyReachableReferences(s.bcv.view, s'.bcv.view, redirect.parentref)
      ensures ref in G.ReachableReferences(s.bcv.view, redirect.parentref)
    {
      var path :| G.NewPath(s.bcv.view, s'.bcv.view, redirect.parentref, path) && Last(path) == ref;
      if ref == path[1] {
        var key :| IMapsTo(redirect.new_parent.children, key, ref);
        assert key !in redirect.keys;
        assert G.IsPath(s.bcv.view, [redirect.parentref, ref]);
      } else {
        var new_childref := path[|path|-2];
        var new_child := redirect.new_children[new_childref];
        assert new_childref in redirect.new_children;
        assert ref in redirect.new_children[new_childref].children.Values;
        var key :| IMapsTo(redirect.new_parent.children, key, new_childref) && IMapsTo(new_child.children, key, ref) && key in redirect.keys && key in redirect.old_parent.children;
        var old_childref := redirect.old_parent.children[key];
        var i :| 0 <= i < |redirect.old_childrefs| && redirect.old_childrefs[i] == old_childref;
        assert BI.ReadStep(s.bcv, RedirectReads(redirect)[i+1]);
        assert G.IsPath(s.bcv.view, [redirect.parentref, old_childref, ref]);
      }
    }

    forall path |
      && IsPath(s'.bcv.view, path)
      && (forall i :: 0 <= i < |path| ==> path[i] in s'.bcv.view.Keys - s.bcv.view.Keys)
    ensures !IsCycle(s'.bcv.view, path)
    {
      if (IsCycle(s'.bcv.view, path)) {
        RedirectOnlyPredOfChildIsParent(s, s', redirect, Last(path), path[0]);
        assert false;
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
        assert G.Root() !in G.Successors(s'.bcv.view[ref]);
      } else if ref in redirect.old_childrefs {
        assert ref in s.bcv.view;
        assert G.Root() !in G.Successors(s'.bcv.view[ref]);
      } else if ref in redirect.new_childrefs {
        assert ref in redirect.new_children;
        if G.Root() in G.Successors(s'.bcv.view[ref]) {
          assert G.Root() in redirect.new_children[ref].children.Values;
          var key :| (
              && IMapsTo(redirect.new_parent.children, key, ref)
              && IMapsTo(redirect.new_children[ref].children, key, Root())
              && key in redirect.keys
              && key in redirect.old_parent.children
          );
          //assert key in redirect.keys * redirect.old_parent.children.Keys;
          //assert redirect.old_children[redirect.old_parent.children[key]].children[key] == Root();
          var old_childref := redirect.old_parent.children[key];
          var i :| 0 <= i < |redirect.old_childrefs| && redirect.old_childrefs[i] == old_childref;
          assert BI.ReadStep(s.bcv, RedirectReads(redirect)[i+1]);
          //assert s.bcv.view[redirect.old_parent.children[key]] == 
          //    redirect.old_children[redirect.old_parent.children[key]];
          //assert Root() in G.Successors(redirect.old_children[redirect.old_parent.children[key]]);
          assert false;
        }
      } else {
        //assert ref in s'.bcv.view.Keys;
        assert ref !in redirect.new_children.Keys;
        //assert ref in s.bcv.view;
        assert G.Root() !in G.Successors(s'.bcv.view[ref]);
      }
    }
  }

  //
  // Preservation proofs
  //

  lemma LookupAfterFirstHasNoRoot(s: Variables, lookup: Lookup, key: UKey)
  requires Inv(s)
  requires IsPathLookup(s.bcv.view, key, lookup)
  ensures forall i | 1 <= i < |lookup| :: lookup[i].ref != Root()
  {
    forall i | 1 <= i < |lookup|
    ensures lookup[i].ref != Root()
    {
      assert LookupFollowsChildRefAtLayer(key, lookup, i-1);
    }
  }
  
  lemma GrowPreservesLookups(s: Variables, s': Variables, start: Reference, oldroot: Node, newchildref: Reference)
  requires Inv(s)
  requires Grow(s.bcv, s'.bcv, oldroot, newchildref)
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
          ReadOp(rootref, newroot),
          ReadOp(newchildref, oldroot)
        ] + lookup[1..];

        InterpretLookupAdditive([ ReadOp(rootref, newroot), ReadOp(newchildref, oldroot) ], lookup[1..], key);
        InterpretLookupAdditive([lookup[0]], lookup[1..], key);
        assert [lookup[0]] + lookup[1..] == lookup;

        forall i | 0 <= i < |lookup'|-1
          ensures LookupFollowsChildRefAtLayer(key, lookup', i)
        {
          if i == 0 {
          } else {
            assert LookupFollowsChildRefAtLayer(key, lookup, i-1);
          }
        }

        assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start);
      } else {
        LookupAfterFirstHasNoRoot(s, lookup, key);
        assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup, start);
      }
    }
  }

  ////////
  //////// Flush
  ////////

  lemma PropagateInterperetation(lookup:Lookup, lookup':Lookup, i:int, middle:Lookup, middle':Lookup, key:UKey)
    requires 0 <= i < |lookup|-1
    requires |lookup'| == |lookup|
    requires lookup[..i] == lookup'[..i]
    requires lookup[i+2..] == lookup'[i+2..]
    requires lookup == lookup[..i] + middle + lookup[i+2..]
    requires lookup' == lookup'[..i] + middle' + lookup'[i+2..]
    requires LookupVisitsWFNodes(lookup)
    requires LookupVisitsWFNodes(middle)
    requires LookupVisitsWFNodes(middle')
    requires InterpretLookup(middle, key) == InterpretLookup(middle', key)
    ensures LookupVisitsWFNodes(lookup')
    ensures InterpretLookup(lookup, key) == InterpretLookup(lookup', key)
  {
    InterpretLookupAdditive3(lookup[..i], middle, lookup[i+2..], key);
    InterpretLookupAdditive3(lookup'[..i], middle', lookup'[i+2..], key);
  }

  lemma FlushPreservesLookups(s: Variables, s': Variables, start: Reference, flush:NodeFlush)
  requires Inv(s)
  requires Flush(s.bcv, s'.bcv, flush)
  ensures PreservesLookups(s, s', start)
  {
    var f := flush;
    var newbuffer := imap k :: (if k in f.flushedKeys then G.M.Merge(f.parent.buffer[k], f.child.buffer[k]) else f.child.buffer[k]);
    var newchild := Node(f.child.children, newbuffer);
    var newparentbuffer := imap k :: (if k in f.flushedKeys then G.M.Update(G.M.NopDelta()) else f.parent.buffer[k]);
    var newparentchildren := imap k | k in f.parent.children :: (if k in f.movedKeys then f.newchildref else f.parent.children[k]);
    var newparent := Node(newparentchildren, newparentbuffer);

    forall lookup:Lookup, key, value | IsSatisfyingLookupFrom(s.bcv.view, key, value, lookup, start)
      ensures exists lookup':Lookup :: IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start)
    {
      if parentLayer :| 0 <= parentLayer < |lookup| && lookup[parentLayer].ref == f.parentref {
        if key !in f.movedKeys {
          var lookup' := lookup[parentLayer := ReadOp(f.parentref, newparent)];
          forall j | 0 <= j < |lookup'|
          ensures IMapsTo(s'.bcv.view, lookup'[j].ref, lookup'[j].node) {
            if (j == parentLayer) {
              assert IMapsTo(s'.bcv.view, lookup'[j].ref, lookup'[j].node);
            } else {
              assert IMapsTo(s'.bcv.view, lookup'[j].ref, lookup'[j].node);
            }
          }
          assert lookup[..parentLayer] + [lookup[parentLayer]] + lookup[parentLayer+1..] == lookup; // observe
          assert lookup'[..parentLayer] + [lookup'[parentLayer]] + lookup'[parentLayer+1..] == lookup'; // observe
          InterpretLookupAdditive3(lookup[..parentLayer], [lookup[parentLayer]], lookup[parentLayer+1..], key);
          InterpretLookupAdditive3(lookup'[..parentLayer], [lookup'[parentLayer]], lookup'[parentLayer+1..], key);
          forall j | 0 <= j < |lookup'|-1
            ensures LookupFollowsChildRefAtLayer(key, lookup', j)
          {
            assert LookupFollowsChildRefAtLayer(key, lookup, j);
          }
          assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start); // observe
        } else {
          if |lookup| - 1 == parentLayer { // we stopped at f.parent
            var lookup' := lookup[..parentLayer] + [ ReadOp(f.parentref, newparent) ] + [ ReadOp(f.newchildref, newchild) ];
            forall j | 0 <= j < |lookup'|
            ensures IMapsTo(s'.bcv.view, lookup'[j].ref, lookup'[j].node) {
            }
            forall j | 0 <= j < |lookup'|-1
              ensures LookupFollowsChildRefAtLayer(key, lookup', j)
            {
              if j <= parentLayer-1 {
                assert LookupFollowsChildRefAtLayer(key, lookup, j);
              }
            }
            assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start); // observe
          } else {
            var middle := [ lookup[parentLayer] ] + [ lookup[parentLayer+1] ];
            var middle' := ([ ReadOp(f.parentref, newparent) ] + [ ReadOp(f.newchildref, newchild) ]);

            assert lookup == lookup[..parentLayer] + middle + lookup[parentLayer+2..];
            var lookup' := lookup[..parentLayer] + middle' + lookup[parentLayer+2..];

            forall j | 0 <= j < |lookup'|
            ensures IMapsTo(s'.bcv.view, lookup'[j].ref, lookup'[j].node) {
              if j == parentLayer {
                assert IMapsTo(s'.bcv.view, lookup'[j].ref, lookup'[j].node);
              } else {
                assert IMapsTo(s'.bcv.view, lookup'[j].ref, lookup'[j].node);
              }
            }

            assert lookup[..parentLayer] == lookup'[..parentLayer];
            assert lookup[parentLayer+2..] == lookup'[parentLayer+2..];

            assert LookupFollowsChildRefAtLayer(key, lookup, parentLayer);    // Handles the j==parentLayer+1 case; connects middle[1] to f.child.
            forall j | 0 <= j < |lookup'|-1
              ensures LookupFollowsChildRefAtLayer(key, lookup', j)
            {
              assert LookupFollowsChildRefAtLayer(key, lookup, j);
            }

            if (key in flush.flushedKeys) {
              assert InterpretLookup([lookup'[parentLayer]], key) == G.M.Update(G.M.NopDelta());
              assert InterpretLookup(middle, key) == InterpretLookup(middle', key);
            } else {
              assert InterpretLookup(middle, key) == InterpretLookup(middle', key);
            }

            PropagateInterperetation(lookup, lookup', parentLayer, middle, middle', key);

            assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start); // observe
          }
        }
      } else {
        assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup, start);
      }
    }
  }


  ////////
  //////// Redirect
  ////////

  lemma RedirectPreservesLookups(s: Variables, s': Variables, start: Reference, redirect: Redirect)
    requires Inv(s)
    requires Redirect(s.bcv, s'.bcv, redirect)
    ensures PreservesLookups(s, s', start)
  {
    forall lookup:Lookup, key, value | IsSatisfyingLookupFrom(s.bcv.view, key, value, lookup, start)
      ensures exists lookup':Lookup :: IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start)
    {
      if i :| 0 <= i < |lookup| && lookup[i].ref == redirect.parentref {
        if key in redirect.keys && i < |lookup| - 1 {
          var new_childref := redirect.new_parent.children[key];
          var new_child := redirect.new_children[new_childref];
          var lookup' := lookup[i := G.ReadOp(redirect.parentref, redirect.new_parent)][i+1 := G.ReadOp(new_childref, new_child)];

          assert LookupFollowsChildRefAtLayer(key, lookup, i);
          var old_childref := redirect.old_parent.children[key];
          var old_child := redirect.old_children[old_childref];
          var idx :| 0 <= idx < |redirect.old_childrefs| && redirect.old_childrefs[idx] == old_childref;
          assert BI.ReadStep(s.bcv, RedirectReads(redirect)[idx+1]);
          assert lookup[i+1].ref == old_childref;
          assert lookup[i+1].node == old_child;
          
          forall j | 0 <= j < |lookup'|-1
            ensures LookupFollowsChildRefAtLayer(key, lookup', j)
          {
            if j == i {
              //assert LookupFollowsChildRefAtLayer(key, lookup, i);
            } else if j == i + 1 {
              assert LookupFollowsChildRefAtLayer(key, lookup, i+1);
            } else {
              assert LookupFollowsChildRefAtLayer(key, lookup, j);
            }
          }

          var middle :=  [lookup[i]]  + [lookup[i+1]];
          var middle' := [lookup'[i]] + [lookup'[i+1]];

          assert lookup[i].node.buffer == lookup'[i].node.buffer;

          assert LookupFollowsChildRefAtLayer(key, lookup, i);
          assert lookup[i+1].node == old_child;
          assert lookup[i+1].node.buffer[key] == lookup'[i+1].node.buffer[key];
          
          assert InterpretLookup(middle', key) == InterpretLookup(middle, key);          
          
          InterpretLookupAdditive3(lookup'[..i], middle', lookup'[i+2..], key);
          assert lookup' == lookup'[..i] + middle' + lookup'[i+2..];
          
          InterpretLookupAdditive3(lookup[..i], middle, lookup[i+2..], key);
          assert middle == lookup[i..i+2];
          assert lookup == lookup[..i] + middle + lookup[i+2..];

          RedirectResultingGraph(s, s', redirect);
          assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start);
        } else {
          var lookup' := lookup[i := G.ReadOp(redirect.parentref, redirect.new_parent)];
          forall j | 0 <= j < |lookup'|-1
            ensures LookupFollowsChildRefAtLayer(key, lookup', j)
          {
            assert LookupFollowsChildRefAtLayer(key, lookup, j);
          }

          InterpretLookupAdditive3(lookup'[..i], [lookup'[i]], lookup'[i+1..], key);
          assert lookup' == lookup'[..i] + [lookup'[i]] + lookup'[i+1..];
          
          InterpretLookupAdditive3(lookup[..i], [lookup[i]], lookup[i+1..], key);
          assert lookup == lookup[..i] + [lookup[i]] + lookup[i+1..];
          
          RedirectResultingGraph(s, s', redirect);
          assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start);
          
        }
      } else {
        RedirectResultingGraph(s, s', redirect);
        assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup, start);
      }
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
    ensures IsSatisfyingLookupFrom(s.bcv.view, key, G.M.DefaultValue(), [ReadOp(Root(), EmptyNode())], Root());
    {
    }
    forall key, lookup:Lookup | IsPathLookup(s.bcv.view, key, lookup)
      ensures LookupIsAcyclic(lookup)
    {
      assert lookup[0].ref == Root();
      forall i, j | 0 <= i < |lookup| && 0 <= j < |lookup| && i != j
        ensures lookup[i].ref == lookup[j].ref
      {
          assert LookupFollowsChildRefAtLayer(key, lookup, 0);
      }
    }
  }

  lemma QueryStepPreservesInvariant(s: Variables, s': Variables)
    requires Inv(s)
    requires BI.OpTransaction(s.bcv, s'.bcv, [])
    ensures Inv(s')
  {
  }

  lemma InsertMessagePreservesAcyclicAndReachablePointersValid(s: Variables, s': Variables, key: UKey, msg: BufferEntry, oldroot: Node)
    requires Inv(s)
    requires InsertMessage(s.bcv, s'.bcv, key, msg, oldroot)
    ensures G.IsAcyclic(s'.bcv.view)
    ensures Acyclic(s')
  {
    G.LocalEditPreservesAcyclic(s.bcv.view, s'.bcv.view, G.Root());
    AcyclicGraphImpliesAcyclic(s');
  }

  lemma InsertMessagePreservesLookupsPut(s: Variables, s': Variables, key: UKey, msg: BufferEntry, oldroot: Node)
    requires Inv(s)
    requires InsertMessage(s.bcv, s'.bcv, key, msg, oldroot)
    requires msg.Define?
    //ensures forall key1 | MS.InDomain(key1) :: KeyHasSatisfyingLookup(s'.bcv.view, key1)
    ensures PreservesLookupsPut(s, s', key, msg.value);
  {
    forall lookup:Lookup, key1, value | key1 != key && IsSatisfyingLookupFrom(s.bcv.view, key1, value, lookup, Root())
      ensures exists lookup':Lookup :: IsSatisfyingLookupFrom(s'.bcv.view, key1, value, lookup', Root())
    {
      var lookup' := Apply((x: Layer) => x.(node := if x.ref in s'.bcv.view then s'.bcv.view[x.ref] else EmptyNode()), lookup);
      InterpsEqualOfAllBuffersEqual(lookup, lookup', key1);

      assert BufferDefinesValue(InterpretLookup(lookup', key1), value);

      forall idx | ValidLayerIndex(lookup', idx) && idx < |lookup'| - 1
      ensures key1 in lookup'[idx].node.children
      ensures LookupFollowsChildRefAtLayer(key1, lookup', idx)
      {
        assert LookupFollowsChildRefAtLayer(key1, lookup, idx);
      }

      assert IsSatisfyingLookupFrom(s'.bcv.view, key1, value, lookup', Root());
    }

    {
      assert KeyHasSatisfyingLookup(s.bcv.view, key, Root());
      var value, lookup: Lookup :| IsSatisfyingLookupFrom(s.bcv.view, key, value, lookup, Root());
      var lookup' := Apply((x: Layer) => x.(node := if x.ref in s'.bcv.view then s'.bcv.view[x.ref] else EmptyNode()), lookup);
      assert lookup' == [lookup'[0]] + lookup'[1..];
      InterpretLookupAdditive([lookup'[0]], lookup'[1..], key);
      assert lookup[1..] == lookup'[1..];
      G.M.MergeIsAssociative(msg, InterpretLookup([lookup[0]], key), InterpretLookup(lookup[1..], key));
      InterpretLookupAdditive([lookup[0]], lookup[1..], key);
      assert lookup == [lookup[0]] + lookup[1..];
      var message' := G.M.Merge(msg, InterpretLookup(lookup, key));

      forall idx | ValidLayerIndex(lookup', idx) && idx < |lookup'| - 1
      ensures key in lookup'[idx].node.children
      ensures LookupFollowsChildRefAtLayer(key, lookup', idx)
      {
        assert LookupFollowsChildRefAtLayer(key, lookup, idx);
      }

      assert IsSatisfyingLookupFrom(s'.bcv.view, key, message'.value, lookup', Root());
    }
  }

  lemma InsertMessagePreservesNonrootLookups(s: Variables, s': Variables, key: UKey, msg: BufferEntry, oldroot: Node, start: Reference)
    requires Inv(s)
    requires InsertMessage(s.bcv, s'.bcv, key, msg, oldroot)
    requires start != Root()
    ensures PreservesLookups(s, s', start)
  {
    forall lookup:Lookup, key, value | IsSatisfyingLookupFrom(s.bcv.view, key, value, lookup, start)
    ensures exists lookup':Lookup :: IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start)
    {
      LookupAfterFirstHasNoRoot(s, lookup, key);
      var lookup' := lookup;
      assert IsSatisfyingLookupFrom(s'.bcv.view, key, value, lookup', start);
    }
  }
    
  lemma InsertMessageStepPreservesInvariant(s: Variables, s': Variables, key: UKey, msg: BufferEntry, oldroot: Node)
    requires Inv(s)
    requires InsertMessage(s.bcv, s'.bcv, key, msg, oldroot)
    // We can have this msg.Define? condition becasue right now the uiop condition
    // enforces that the inserted message must be a Define. Eventually we'll need
    // to expand the semantics of the map and the proof to support non-Define messages.
    requires msg.Define?
    ensures Inv(s')
  {
    InsertMessagePreservesAcyclicAndReachablePointersValid(s, s', key, msg, oldroot);
    InsertMessagePreservesLookupsPut(s, s', key, msg, oldroot);
  }

  lemma FlushStepPreservesInvariant(s: Variables, s': Variables, flush:NodeFlush)
    requires Inv(s)
    requires Flush(s.bcv, s'.bcv, flush)
    ensures Inv(s')
  {
    FlushPreservesAcyclic(s, s', flush);
    FlushPreservesLookups(s, s', Root(), flush);
  }
  
  lemma GrowStepPreservesInvariant(s: Variables, s': Variables, oldroot: Node, newchildref: Reference)
    requires Inv(s)
    requires Grow(s.bcv, s'.bcv, oldroot, newchildref)
    ensures Inv(s')
  {
    GrowPreservesAcyclic(s, s', oldroot, newchildref);
    GrowPreservesLookups(s, s', Root(), oldroot, newchildref);
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

  // Query Descent

  /*lemma QueryDescentStepPreservesInvariant(s: Variables, s': Variables, qd: QueryDescent)
    requires Inv(s)
    requires QueryDescent(s.bcv, s'.bcv, qd)
    ensures Inv(s')
  {
  }*/


  // GC Step

  lemma GCStepPreservesIsPathLookup(s: Variables, s': Variables, refs: iset<Reference>, lookup: Lookup, key: UKey)
    requires Inv(s)
    requires BI.GC(s.bcv, s'.bcv, refs)
    requires IsPathLookup(s.bcv.view, key, lookup);
    requires lookup[0].ref !in refs
    ensures IsPathLookup(s'.bcv.view, key, lookup);
  {
    if |lookup| == 1 {
    } else {
      var lookup' := DropLast(lookup);
      forall idx | 0 <= idx < |lookup'| - 1
      ensures LookupFollowsChildRefAtLayer(key, lookup', idx)
      {
        assert LookupFollowsChildRefAtLayer(key, lookup, idx);
      }
      GCStepPreservesIsPathLookup(s, s', refs, lookup', key);
      assert LookupFollowsChildRefAtLayer(key, lookup, |lookup| - 2);
      // by the closure requirement, since `prev` isn't in `refs`,
      // `last` shouldn't be either:
      //var prev := lookup[|lookup|-2].ref;
      //var last := lookup[|lookup|-1].ref;
      //assert prev !in refs;
      //assert s.bcv.view[prev] == lookup[|lookup|-2].node;
      //assert last in Successors(s.bcv.view[prev]);
      //assert prev in BI.Predecessors(s.bcv.view, last);
      //assert last !in refs;
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
      GCStepPreservesIsPathLookup(s, s', refs, lookup, key);
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
      case BetreeInsert(ins) => InsertMessageStepPreservesInvariant(s, s', ins.key, ins.msg, ins.oldroot);
      case BetreeFlush(flush) => FlushStepPreservesInvariant(s, s', flush);
      case BetreeGrow(growth) => GrowStepPreservesInvariant(s, s', growth.oldroot, growth.newchildref);
      case BetreeRedirect(redirect) => RedirectStepPreservesInvariant(s, s', redirect);
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
