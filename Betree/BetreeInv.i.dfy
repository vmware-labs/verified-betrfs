include "../lib/Base/Maps.s.dfy"
include "../lib/Base/sequences.i.dfy"
include "../MapSpec/MapSpec.s.dfy"
include "../Betree/Betree.i.dfy"
//
// Invariants about Betrees: lookup structure, non-equivocation, and
// preservation. 
// TODO(jonh) and apparently a bunch of dead code! See TODO inline.
//
  
module BetreeInv {
  import opened DB = Betree
  import opened Maps
  import opened Sequences
  import opened BetreeSpec`Internal
  import opened G = BetreeSpec.G
  import opened Options
  import opened KeyType
  import opened ValueType
  import UI

  predicate KeyHasSatisfyingLookup(k: Constants, view: BI.View, key: Key)
  {
    exists lookup, value :: IsSatisfyingLookup(k, view, key, value, lookup)
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
  
  predicate Acyclic(k: Constants, s: Variables) {
    forall key, lookup ::
      IsPathFromRootLookup(k, s.bcv.view, key, lookup) ==>
      LookupIsAcyclic(lookup)
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && BI.Inv(k.bck, s.bcv)
    && G.IsAcyclic(s.bcv.view)
    && Acyclic(k, s)
    && (forall key | MS.InDomain(key) :: KeyHasSatisfyingLookup(k, s.bcv.view, key))
  }

  //// Definitions for lookup preservation

  // One-way preservation

  predicate PreservesLookups(k: Constants, s: Variables, s': Variables)
  {
    forall lookup, key, value :: IsSatisfyingLookup(k, s.bcv.view, key, value, lookup) ==>
      exists lookup' :: IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
  }

  predicate PreservesLookupsExcept(k: Constants, s: Variables, s': Variables, exceptQuery: Key)
  {
    forall lookup, key, value :: key != exceptQuery && IsSatisfyingLookup(k, s.bcv.view, key, value, lookup) ==>
      exists lookup' :: IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
  }

  // TODO generalize this to explain how the value changes when a non-Define
  // message is inserted
  predicate PreservesLookupsPut(k: Constants, s: Variables, s': Variables, key: Key, value: Value)
  {
    && PreservesLookupsExcept(k, s, s', key)
    && exists lookup :: IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup)
  }

  //

  lemma InterpsEqualOfAllBuffersEqual(a: Lookup, b: Lookup, key: Key)
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

  lemma InterpretLookupAdditive(a: Lookup, b: Lookup, key: Key)
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

  lemma InterpretLookupAdditive3(a: Lookup, b: Lookup, c: Lookup, key: Key)
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

  lemma SatisfyingLookupsForKeyAgree(k: Constants, s: Variables, key: Key, value: Value, value': Value, lookup: Lookup, lookup': Lookup, idx: int)
  requires IsSatisfyingLookup(k, s.bcv.view, key, value, lookup);
  requires IsSatisfyingLookup(k, s.bcv.view, key, value', lookup');
  requires 0 <= idx < |lookup|;
  requires 0 <= idx < |lookup'|;
  ensures lookup[idx] == lookup'[idx];
  {
    if (idx == 0) {
    } else {
      SatisfyingLookupsForKeyAgree(k, s, key, value, value', lookup, lookup', idx - 1);
      assert LookupFollowsChildRefAtLayer(key, lookup, idx-1);
      assert LookupFollowsChildRefAtLayer(key, lookup', idx-1);
    }
  }

  lemma CantEquivocateWlog(k: Constants, s: Variables, key: Key, value: Value, value': Value, lookup: Lookup, lookup': Lookup)
  requires IsSatisfyingLookup(k, s.bcv.view, key, value, lookup);
  requires IsSatisfyingLookup(k, s.bcv.view, key, value', lookup');
  requires |lookup| <= |lookup'|
  ensures value == value';
  {

    var junk := lookup'[|lookup|..];
    forall idx | 0 <= idx < |lookup|
    ensures lookup'[idx] == lookup[idx];
    {
        SatisfyingLookupsForKeyAgree(k, s, key, value, value', lookup, lookup', idx);
    }
    assert lookup' == lookup + junk; // observe
    InterpretLookupAdditive(lookup, junk, key);
  }

  lemma CantEquivocate(k: Constants, s: Variables, key: Key, value: Value, value': Value, lookup: Lookup, lookup': Lookup)
  requires IsSatisfyingLookup(k, s.bcv.view, key, value, lookup);
  requires IsSatisfyingLookup(k, s.bcv.view, key, value', lookup');
  ensures value == value';
  {
    if (|lookup| <= |lookup'|) {
      CantEquivocateWlog(k, s, key, value, value', lookup, lookup');
    } else {
      CantEquivocateWlog(k, s, key, value', value, lookup', lookup);
    }
  }

  // Old definitions
  // TODO clean these up; remove them or change them to use BetreeStep objects instead

  predicate InsertMessage(k: BI.Constants, s: BI.Variables, s': BI.Variables, key: Key, msg: BufferEntry, oldroot: Node)
  {
    && ValidInsertion(MessageInsertion(key, msg, oldroot))
    && BI.Reads(k, s, InsertionReads(MessageInsertion(key, msg, oldroot)))
    && BI.OpTransaction(k, s, s', InsertionOps(MessageInsertion(key, msg, oldroot)))
  }

  predicate Flush(k: BI.Constants, s: BI.Variables, s': BI.Variables, flush:NodeFlush)
  {
    && ValidFlush(flush)
    && BI.Reads(k, s, FlushReads(flush))
    && BI.OpTransaction(k, s, s', FlushOps(flush))
  }

  predicate Grow(k: BI.Constants, s: BI.Variables, s': BI.Variables, oldroot: Node, newchildref: Reference)
  {
    && ValidGrow(RootGrowth(oldroot, newchildref))
    && BI.Reads(k, s, GrowReads(RootGrowth(oldroot, newchildref)))
    && BI.OpTransaction(k, s, s', GrowOps(RootGrowth(oldroot, newchildref)))
  }

  predicate Redirect(k: BI.Constants, s: BI.Variables, s': BI.Variables, redirect: Redirect)
  {
    && ValidRedirect(redirect)
    && BI.Reads(k, s, RedirectReads(redirect))
    && BI.OpTransaction(k, s, s', RedirectOps(redirect))
  }

  predicate Query(k: BI.Constants, s: BI.Variables, s': BI.Variables, key: Key, value: Value, lookup: Lookup)
  {
    && ValidQuery(LookupQuery(key, value, lookup))
    && BI.Reads(k, s, QueryReads(LookupQuery(key, value, lookup)))
    && BI.OpTransaction(k, s, s', QueryOps(LookupQuery(key, value, lookup)))
  }

  predicate SuccQuery(k: BI.Constants, s: BI.Variables, s': BI.Variables, start: UI.RangeStart, results: seq<UI.SuccResult>, end: UI.RangeEnd, lookup: Lookup)
  {
    && ValidSuccQuery(BetreeSpec.SuccQuery(start, results, end, lookup))
    && BI.Reads(k, s, SuccQueryReads(BetreeSpec.SuccQuery(start, results, end, lookup)))
    && BI.OpTransaction(k, s, s', SuccQueryOps(BetreeSpec.SuccQuery(start, results, end, lookup)))
  }

  //
  // Acyclicity proofs
  //
  
  lemma AcyclicGraphImpliesAcyclic(k: Constants, s: Variables)
    requires IsAcyclic(s.bcv.view)
    ensures Acyclic(k, s)
  {
    var g := s.bcv.view;
    forall key, lookup: Lookup | IsPathFromRootLookup(k, s.bcv.view, key, lookup)
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

//~  lemma InsertMessagePreservesAcyclic(k: Constants, s: Variables, s': Variables, key: Key, msg: BufferEntry, oldroot: Node)
//~    requires Inv(k, s)
//~    requires InsertMessage(k.bck, s.bcv, s'.bcv, key, msg, oldroot)
//~    ensures Acyclic(k, s')
//~  {
//~    G.LocalEditPreservesAcyclic(s.bcv.view, s'.bcv.view, Root());
//~    AcyclicGraphImpliesAcyclic(k, s');
//~  }

  lemma FlushPreservesAcyclic(k: Constants, s: Variables, s': Variables, flush:NodeFlush)
    requires Inv(k, s)
    requires Flush(k.bck, s.bcv, s'.bcv, flush)
    ensures G.IsAcyclic(s'.bcv.view)
    ensures Acyclic(k, s')
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
    AcyclicGraphImpliesAcyclic(k, s');
  }

  lemma GrowPreservesAcyclic(k: Constants, s: Variables, s': Variables, oldroot: Node, newchildref: Reference)
    requires Inv(k, s)
    requires Grow(k.bck, s.bcv, s'.bcv, oldroot, newchildref)
    ensures G.IsAcyclic(s'.bcv.view)
    ensures Acyclic(k, s')
  {
    forall ref | ref in G.NewlyReachableReferences(s.bcv.view, s'.bcv.view, Root())
      ensures ref in G.ReachableReferences(s.bcv.view, Root())
    {
      var path :| G.NewPath(s.bcv.view, s'.bcv.view, Root(), path) && Last(path) == ref;
      assert path[|path|-2] == newchildref;
      assert G.IsPath(s.bcv.view, [Root(), ref]);
     }
    G.LocalEditPreservesAcyclic(s.bcv.view, s'.bcv.view, Root());
    AcyclicGraphImpliesAcyclic(k, s');
  }

  lemma RedirectResultingGraphAfterAllocs(k: BI.Constants, s: BI.Variables, s': BI.Variables, childrefs: seq<Reference>, children: imap<Reference, Node>)
  requires forall ref :: ref in childrefs ==> ref in children
  requires BI.Inv(k, s)
  requires BI.OpTransaction(k, s, s', RedirectChildAllocs(childrefs, children))
  ensures BI.Inv(k, s')
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
      var smid := BI.GetPenultimateState(k, s, s', ops);
      RedirectResultingGraphAfterAllocs(k, s, smid, DropLast(childrefs), children);
      assert s'.view.Keys - s.view.Keys
          == (smid.view.Keys + iset{Last(childrefs)}) - s.view.Keys
          == (smid.view.Keys - s.view.Keys) + iset{Last(childrefs)}
          == (iset r | r in DropLast(childrefs)) + iset{Last(childrefs)}
          == (iset r | r in childrefs);
    }
  }

  lemma RedirectResultingGraph(k: Constants, s: Variables, s': Variables, redirect: Redirect)
  requires Inv(k, s);
  requires Redirect(k.bck, s.bcv, s'.bcv, redirect);
  ensures IMapsTo(s'.bcv.view, redirect.parentref, redirect.new_parent);
  ensures forall childref | childref in redirect.new_childrefs :: IMapsTo(s'.bcv.view, childref, redirect.new_children[childref])
  ensures forall childref | childref in redirect.new_childrefs :: childref !in s.bcv.view
  ensures s'.bcv.view.Keys - s.bcv.view.Keys == redirect.new_children.Keys
  ensures forall ref | ref in s.bcv.view && ref != redirect.parentref :: IMapsTo(s'.bcv.view, ref, s.bcv.view[ref])
  {
    var ops := RedirectOps(redirect);
    var smid := BI.GetPenultimateState(k.bck, s.bcv, s'.bcv, ops);
    RedirectResultingGraphAfterAllocs(k.bck, s.bcv, smid, redirect.new_childrefs, redirect.new_children);
    assert s'.bcv.view.Keys == smid.view.Keys;
  }

  lemma RedirectOnlyPredOfChildIsParent(k: Constants, s: Variables, s': Variables, redirect: Redirect, parentref: Reference, ref: Reference)
  requires Inv(k, s);
  requires Redirect(k.bck, s.bcv, s'.bcv, redirect);
  requires ref in redirect.new_children
  requires parentref in s'.bcv.view
  requires ref in Successors(s'.bcv.view[parentref])
  ensures parentref == redirect.parentref
  {
    RedirectResultingGraph(k, s, s', redirect);
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
      assert BI.ReadStep(k.bck, s.bcv, RedirectReads(redirect)[i+1]);

      assert ref in s.bcv.view;
      assert false;
    } else {
      assert false;
    }
  }

  lemma RedirectPreservesAcyclic(k: Constants, s: Variables, s': Variables, redirect: Redirect)
    requires Inv(k, s);
    requires Redirect(k.bck, s.bcv, s'.bcv, redirect);
    ensures Acyclic(k, s');
    ensures G.IsAcyclic(s'.bcv.view);
  {
    RedirectResultingGraph(k, s, s', redirect);

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
        assert BI.ReadStep(k.bck, s.bcv, RedirectReads(redirect)[i+1]);
        assert G.IsPath(s.bcv.view, [redirect.parentref, old_childref, ref]);
      }
    }

    forall path |
      && IsPath(s'.bcv.view, path)
      && (forall i :: 0 <= i < |path| ==> path[i] in s'.bcv.view.Keys - s.bcv.view.Keys)
    ensures !IsCycle(s'.bcv.view, path)
    {
      if (IsCycle(s'.bcv.view, path)) {
        RedirectOnlyPredOfChildIsParent(k, s, s', redirect, Last(path), path[0]);
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
        assert BI.ReadStep(k.bck, s.bcv, RedirectReads(redirect)[i+1]);

        assert path[0] in s.bcv.view;
        assert false;
        */
      }
    }

    G.LocalEditPreservesAcyclic(s.bcv.view, s'.bcv.view, redirect.parentref); // observe
    AcyclicGraphImpliesAcyclic(k, s'); // observe
  }

  //
  // Preservation proofs
  //
  
  lemma GrowPreservesLookups(k: Constants, s: Variables, s': Variables, oldroot: Node, newchildref: Reference)
  requires Inv(k, s)
  requires Grow(k.bck, s.bcv, s'.bcv, oldroot, newchildref)
  ensures PreservesLookups(k, s, s')
  {
    forall lookup:Lookup, key, value | IsSatisfyingLookup(k, s.bcv.view, key, value, lookup)
    ensures exists lookup' :: IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
    {
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
      
      assert IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup');
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
    requires InterpretLookup(middle, key) == InterpretLookup(middle', key)
    ensures LookupVisitsWFNodes(lookup')
    ensures InterpretLookup(lookup, key) == InterpretLookup(lookup', key)
  {
    InterpretLookupAdditive3(lookup[..i], middle, lookup[i+2..], key);
    InterpretLookupAdditive3(lookup'[..i], middle', lookup'[i+2..], key);
  }

  lemma FlushPreservesLookups(k: Constants, s: Variables, s': Variables, flush:NodeFlush)
  requires Inv(k, s)
  requires Flush(k.bck, s.bcv, s'.bcv, flush)
  ensures PreservesLookups(k, s, s')
  {
    var f := flush;
    var newbuffer := imap k :: (if k in f.flushedKeys then G.M.Merge(f.parent.buffer[k], f.child.buffer[k]) else f.child.buffer[k]);
    var newchild := Node(f.child.children, newbuffer);
    var newparentbuffer := imap k :: (if k in f.flushedKeys then G.M.Update(G.M.NopDelta()) else f.parent.buffer[k]);
    var newparentchildren := imap k | k in f.parent.children :: (if k in f.movedKeys then f.newchildref else f.parent.children[k]);
    var newparent := Node(newparentchildren, newparentbuffer);

    forall lookup:Lookup, key, value | IsSatisfyingLookup(k, s.bcv.view, key, value, lookup)
      ensures exists lookup' :: IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
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
          assert IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup'); // observe
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
            assert IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup'); // observe
          } else {
            var middle := [ lookup[parentLayer] ] + [ lookup[parentLayer+1] ];
            var middle' := ([ ReadOp(f.parentref, newparent) ] + [ ReadOp(f.newchildref, newchild) ]);

            assert lookup == lookup[..parentLayer] + middle + lookup[parentLayer+2..];
            var lookup' := lookup[..parentLayer] + middle' + lookup[parentLayer+2..];

            forall j | 0 <= j < |lookup'|
            ensures IMapsTo(s'.bcv.view, lookup'[j].ref, lookup'[j].node) {
              if j == parentLayer { }   // case split.
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

            assert IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup'); // observe
          }
        }
      } else {
        assert IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup);
      }
    }
  }


  ////////
  //////// Redirect
  ////////

  lemma RedirectPreservesLookups(k: Constants, s: Variables, s': Variables, redirect: Redirect)
    requires Inv(k, s)
    requires Redirect(k.bck, s.bcv, s'.bcv, redirect)
    ensures PreservesLookups(k, s, s')
  {
    forall lookup:Lookup, key, value | IsSatisfyingLookup(k, s.bcv.view, key, value, lookup)
      ensures exists lookup' :: IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
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
          assert BI.ReadStep(k.bck, s.bcv, RedirectReads(redirect)[idx+1]);
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

          RedirectResultingGraph(k, s, s', redirect);
          assert IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup');
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
          
          RedirectResultingGraph(k, s, s', redirect);
          assert IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup');
          
        }
      } else {
        RedirectResultingGraph(k, s, s', redirect);
        assert IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup);
      }
    }
  }
  
  ////////
  //////// Invariant proofs
  ////////

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
    forall key | MS.InDomain(key)
    ensures IsSatisfyingLookup(k, s.bcv.view, key, G.M.DefaultValue(), [ReadOp(Root(), EmptyNode())]);
    {
    }
    forall key, lookup:Lookup | IsPathFromRootLookup(k, s.bcv.view, key, lookup)
      ensures LookupIsAcyclic(lookup)
    {
      forall i, j | 0 <= i < |lookup| && 0 <= j < |lookup| && i != j
        ensures lookup[i].ref == lookup[j].ref
      {
          assert LookupFollowsChildRefAtLayer(key, lookup, 0);
      }
    }
  }

  lemma QueryStepPreservesInvariant(k: Constants, s: Variables, s': Variables)
    requires Inv(k, s)
    requires BI.OpTransaction(k.bck, s.bcv, s'.bcv, [])
    ensures Inv(k, s')
  {
  }

  lemma InsertMessagePreservesAcyclicAndReachablePointersValid(k: Constants, s: Variables, s': Variables, key: Key, msg: BufferEntry, oldroot: Node)
    requires Inv(k, s)
    requires InsertMessage(k.bck, s.bcv, s'.bcv, key, msg, oldroot)
    ensures G.IsAcyclic(s'.bcv.view)
    ensures Acyclic(k, s')
  {
    G.LocalEditPreservesAcyclic(s.bcv.view, s'.bcv.view, G.Root());
    AcyclicGraphImpliesAcyclic(k, s');
  }

  lemma InsertMessagePreservesLookupsPut(k: Constants, s: Variables, s': Variables, key: Key, msg: BufferEntry, oldroot: Node)
    requires Inv(k, s)
    requires InsertMessage(k.bck, s.bcv, s'.bcv, key, msg, oldroot)
    requires msg.Define?
    //ensures forall key1 | MS.InDomain(key1) :: KeyHasSatisfyingLookup(k, s'.bcv.view, key1)
    ensures PreservesLookupsPut(k, s, s', key, msg.value);
  {
    forall lookup, key1, value | key1 != key && IsSatisfyingLookup(k, s.bcv.view, key1, value, lookup)
      ensures exists lookup' :: IsSatisfyingLookup(k, s'.bcv.view, key1, value, lookup')
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

      assert IsSatisfyingLookup(k, s'.bcv.view, key1, value, lookup');
    }

    {
      assert KeyHasSatisfyingLookup(k, s.bcv.view, key);
      var value, lookup: Lookup :| IsSatisfyingLookup(k, s.bcv.view, key, value, lookup);
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

      assert IsSatisfyingLookup(k, s'.bcv.view, key, message'.value, lookup');
    }
  }
    
  lemma InsertMessageStepPreservesInvariant(k: Constants, s: Variables, s': Variables, key: Key, msg: BufferEntry, oldroot: Node)
    requires Inv(k, s)
    requires InsertMessage(k.bck, s.bcv, s'.bcv, key, msg, oldroot)
    // We can have this msg.Define? condition becasue right now the uiop condition
    // enforces that the inserted message must be a Define. Eventually we'll need
    // to expand the semantics of the map and the proof to support non-Define messages.
    requires msg.Define?
    ensures Inv(k, s')
  {
    InsertMessagePreservesAcyclicAndReachablePointersValid(k, s, s', key, msg, oldroot);
    InsertMessagePreservesLookupsPut(k, s, s', key, msg, oldroot);
  }

  lemma FlushStepPreservesInvariant(k: Constants, s: Variables, s': Variables, flush:NodeFlush)
    requires Inv(k, s)
    requires Flush(k.bck, s.bcv, s'.bcv, flush)
    ensures Inv(k, s')
  {
    FlushPreservesAcyclic(k, s, s', flush);
    FlushPreservesLookups(k, s, s', flush);
  }
  
  lemma GrowStepPreservesInvariant(k: Constants, s: Variables, s': Variables, oldroot: Node, newchildref: Reference)
    requires Inv(k, s)
    requires Grow(k.bck, s.bcv, s'.bcv, oldroot, newchildref)
    ensures Inv(k, s')
  {
    GrowPreservesAcyclic(k, s, s', oldroot, newchildref);
    GrowPreservesLookups(k, s, s', oldroot, newchildref);
  }
 
  // Redirect
  lemma RedirectStepPreservesInvariant(k: Constants, s: Variables, s': Variables, redirect: Redirect)
    requires Inv(k, s)
    requires Redirect(k.bck, s.bcv, s'.bcv, redirect)
    ensures Inv(k, s')
  {
    RedirectPreservesAcyclic(k, s, s', redirect);
    RedirectPreservesLookups(k, s, s', redirect);
    BI.TransactionPreservesInv(k.bck, s.bcv, s'.bcv, RedirectOps(redirect));
  }


  // GC Step

  lemma IsPathFromRootLookupImpliesReachable(k: Constants, s: Variables, key: Key, lookup: Lookup, i: int)
    requires Inv(k, s)
    requires IsPathFromRootLookup(k, s.bcv.view, key, lookup)
    requires 0 <= i < |lookup|
    ensures BI.ReachableReference(k.bck, s.bcv, lookup[i].ref);
  {
    if (i == 0) {
      var l := [lookup[0].ref];
      assert BI.LookupIsValid(k.bck, s.bcv, l) && Last(l) == lookup[0].ref;
      assert BI.ReachableReference(k.bck, s.bcv, lookup[0].ref);
    } else {
      IsPathFromRootLookupImpliesReachable(k, s, key, lookup, i-1);
      var l: BI.Lookup :| BI.LookupIsValid(k.bck, s.bcv, l) && Last(l) == lookup[i-1].ref;
      var l' := l + [lookup[i].ref];
      assert LookupFollowsChildRefAtLayer(key, lookup, i-1);
      assert BI.LookupIsValid(k.bck, s.bcv, l') && Last(l') == lookup[i].ref;
      assert BI.ReachableReference(k.bck, s.bcv, lookup[i].ref);
    }
  }

  lemma GCStepPreservesIsPathFromRootLookup(k: Constants, s: Variables, s': Variables, refs: iset<Reference>, lookup: Lookup, key: Key)
    requires Inv(k, s)
    requires BI.GC(k.bck, s.bcv, s'.bcv, refs)
    requires IsPathFromRootLookup(k, s.bcv.view, key, lookup);
    ensures IsPathFromRootLookup(k, s'.bcv.view, key, lookup);
  {
    forall i | 0 <= i < |lookup|
    ensures IMapsTo(s'.bcv.view, lookup[i].ref, lookup[i].node)
    {
      assert IMapsTo(s.bcv.view, lookup[i].ref, lookup[i].node);
      IsPathFromRootLookupImpliesReachable(k, s, key, lookup, i);
      assert BI.ReachableReference(k.bck, s.bcv, lookup[i].ref);
      assert lookup[i].ref !in refs;
    }
  }

//~  lemma GCStepPreservesIsPathFromRootLookupRev(k: Constants, s: Variables, s': Variables, refs: iset<Reference>, lookup: Lookup, key: Key)
//~    requires Inv(k, s)
//~    requires BI.GC(k.bck, s.bcv, s'.bcv, refs)
//~    requires IsPathFromRootLookup(k, s'.bcv.view, key, lookup);
//~    ensures IsPathFromRootLookup(k, s.bcv.view, key, lookup);
//~  {
//~  }

  lemma GCStepPreservesAcyclicity(k: Constants, s: Variables, s': Variables, refs: iset<Reference>)
    requires Inv(k, s)
    requires BI.GC(k.bck, s.bcv, s'.bcv, refs)
    ensures G.IsAcyclic(s'.bcv.view)
    ensures Acyclic(k, s')
  {
    G.UnallocPreservesAcyclic(s.bcv.view, s'.bcv.view);
    AcyclicGraphImpliesAcyclic(k, s');
  }

  lemma GCStepPreservesLookups(k: Constants, s: Variables, s': Variables, refs: iset<Reference>)
    requires Inv(k, s)
    requires BI.GC(k.bck, s.bcv, s'.bcv, refs)
    ensures PreservesLookups(k, s, s')
  {
    forall lookup:Lookup, key, value | IsSatisfyingLookup(k, s.bcv.view, key, value, lookup)
    ensures exists lookup' :: IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
    {
      GCStepPreservesIsPathFromRootLookup(k, s, s', refs, lookup, key);
      assert IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup);
    }
  }

  lemma GCStepPreservesInvariant(k: Constants, s: Variables, s': Variables, refs: iset<Reference>)
    requires Inv(k, s)
    requires BI.GC(k.bck, s.bcv, s'.bcv, refs)
    ensures Inv(k, s')
  {
    BI.GCPreservesInv(k.bck, s.bcv, s'.bcv, refs);
    GCStepPreservesAcyclicity(k, s, s', refs);
    GCStepPreservesLookups(k, s, s', refs);
  }

  // Putting it all together

  lemma BetreeStepPreservesInvariant(k: Constants, s: Variables, s': Variables, uiop: UI.Op, betreeStep: BetreeStep)
    requires Inv(k, s)
    requires Betree(k, s, s', uiop, betreeStep)
    ensures Inv(k, s')
  {
    match betreeStep {
      case BetreeQuery(q) => QueryStepPreservesInvariant(k, s, s');
      case BetreeSuccQuery(sq) => QueryStepPreservesInvariant(k, s, s');
      case BetreeInsert(ins) => InsertMessageStepPreservesInvariant(k, s, s', ins.key, ins.msg, ins.oldroot);
      case BetreeFlush(flush) => FlushStepPreservesInvariant(k, s, s', flush);
      case BetreeGrow(growth) => GrowStepPreservesInvariant(k, s, s', growth.oldroot, growth.newchildref);
      case BetreeRedirect(redirect) => RedirectStepPreservesInvariant(k, s, s', redirect);
    }
  }

  lemma NextStepPreservesInvariant(k: Constants, s: Variables, s': Variables, uiop: UI.Op, step: Step)
    requires Inv(k, s)
    requires NextStep(k, s, s', uiop, step)
    ensures Inv(k, s')
  {
    match step {
      case GCStep(refs) => GCStepPreservesInvariant(k, s, s', refs);
      case BetreeStep(betreeStep) => BetreeStepPreservesInvariant(k, s, s', uiop, betreeStep);
      case StutterStep => {}
    }
  }
  
  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UI.Op)
    requires Inv(k, s)
    requires Next(k, s, s', uiop)
    ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', uiop, step);
    NextStepPreservesInvariant(k, s, s', uiop, step);
  }
}
