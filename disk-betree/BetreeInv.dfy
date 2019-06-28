include "../lib/Maps.dfy"
include "../lib/sequences.dfy"
include "MapSpec.dfy"
include "Betree.dfy"
  
module BetreeInv {
  import opened DB = Betree
  import opened Maps
  import opened Sequences
  import opened BetreeSpec`Internal
  import opened G = BetreeSpec.G

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

  // Two-way preservation

  predicate EquivalentLookups(k: Constants, s: Variables, s': Variables)
  {
    && PreservesLookups(k, s, s')
    && PreservesLookups(k, s', s)
  }

  predicate EquivalentLookupsWithPut(k: Constants, s: Variables, s': Variables, key: Key, value: Value)
  {
    && PreservesLookupsExcept(k, s, s', key)
    && PreservesLookupsExcept(k, s', s, key)
    && exists lookup :: IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup)
  }

  //

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

  predicate Flush(k: BI.Constants, s: BI.Variables, s': BI.Variables, parentref: Reference, parent: Node, childref: Reference, child: Node, newchildref: Reference, movedKeys: iset<Key>)
  {
    var flush := NodeFlush(parentref, parent, childref, child, newchildref, movedKeys);
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

  predicate Split(k: BI.Constants, s: BI.Variables, s': BI.Variables, fusion: NodeFusion)
  {
    && ValidSplit(fusion)
    && BI.Reads(k, s, SplitReads(fusion))
    && BI.OpTransaction(k, s, s', SplitOps(fusion))
  }

  predicate Merge(k: BI.Constants, s: BI.Variables, s': BI.Variables, fusion: NodeFusion)
  {
    && ValidMerge(fusion)
    && BI.Reads(k, s, MergeReads(fusion))
    && BI.OpTransaction(k, s, s', MergeOps(fusion))
  }

  predicate Query(k: BI.Constants, s: BI.Variables, s': BI.Variables, key: Key, value: Value, lookup: Lookup)
  {
    && ValidQuery(LookupQuery(key, value, lookup))
    && BI.Reads(k, s, QueryReads(LookupQuery(key, value, lookup)))
    && BI.OpTransaction(k, s, s', QueryOps(LookupQuery(key, value, lookup)))
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
      G.AcyclicGraphImpliesSimplePath(g, path);
    }
  }

  lemma InsertMessagePreservesAcyclic(k: Constants, s: Variables, s': Variables, key: Key, msg: BufferEntry, oldroot: Node)
    requires Inv(k, s)
    requires InsertMessage(k.bck, s.bcv, s'.bcv, key, msg, oldroot)
    ensures Acyclic(k, s')
  {
    G.LocalEditPreservesAcyclic(s.bcv.view, s'.bcv.view, Root());
    AcyclicGraphImpliesAcyclic(k, s');
  }

  lemma FlushPreservesAcyclic(k: Constants, s: Variables, s': Variables,
                              parentref: BI.Reference, parent: Node,
                              childref: BI.Reference, child: Node, newchildref: BI.Reference,
                              movedKeys: iset<Key>)
    requires Inv(k, s)
    requires Flush(k.bck, s.bcv, s'.bcv, parentref, parent, childref, child, newchildref, movedKeys)
    ensures Acyclic(k, s')
  {
    forall ref | ref in G.NewlyReachableReferences(s.bcv.view, s'.bcv.view, parentref)
      ensures ref in G.ReachableReferences(s.bcv.view, parentref)
      {
        var path :| G.NewPath(s.bcv.view, s'.bcv.view, parentref, path) && Last(path) == ref;
        if path[1] == ref {
          assert G.IsPath(s.bcv.view, [parentref, ref]);
        } else {
          assert path[|path|-2] == newchildref;
          assert G.IsPath(s.bcv.view, [parentref, childref, ref]);
        }
      }
    G.LocalEditPreservesAcyclic(s.bcv.view, s'.bcv.view, parentref);
    AcyclicGraphImpliesAcyclic(k, s');
  }

  lemma GrowPreservesAcyclic(k: Constants, s: Variables, s': Variables, oldroot: Node, newchildref: Reference)
    requires Inv(k, s)
    requires Grow(k.bck, s.bcv, s'.bcv, oldroot, newchildref)
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

  lemma RedirectPreservesAcyclic(k: Constants, s: Variables, s': Variables, redirect: Redirect)
    requires Inv(k, s);
    requires Redirect(k.bck, s.bcv, s'.bcv, redirect);
    ensures Acyclic(k, s');
  {
    forall ref | ref in G.NewlyReachableReferences(s.bcv.view, s'.bcv.view, redirect.parentref)
      ensures ref in G.ReachableReferences(s.bcv.view, redirect.parentref)
    {
      var path :| G.NewPath(s.bcv.view, s'.bcv.view, redirect.parentref, path) && Last(path) == ref;
      if ref == path[1] {
        var key :| IMapsTo(redirect.new_parent.children, key, ref);
        assert key !in redirect.keys;
        assert G.IsPath(s.bcv.view, [redirect.parentref, ref]);
      } else {
        assert path[|path|-2] == redirect.new_childref;
        assert ref in IMapRestrict(redirect.new_child.children, redirect.keys * redirect.old_parent.children.Keys).Values;
        var key :| key in redirect.keys * redirect.old_parent.children.Keys * redirect.new_child.children.Keys && redirect.new_child.children[key] == ref;
        var old_childref := redirect.old_parent.children[key];
        var i :| 0 <= i < |redirect.old_childrefs| && redirect.old_childrefs[i] == old_childref;
        assert BI.ReadStep(k.bck, s.bcv, RedirectReads(redirect)[i+1]);
        assert G.IsPath(s.bcv.view, [redirect.parentref, old_childref, ref]);
      }
    }
    G.LocalEditPreservesAcyclic(s.bcv.view, s'.bcv.view, redirect.parentref); // observe
    AcyclicGraphImpliesAcyclic(k, s'); // observe
  }

  lemma SplitPreservesAcyclic(k: Constants, s: Variables, s': Variables, fusion: NodeFusion)
    requires Inv(k, s);
    requires Split(k.bck, s.bcv, s'.bcv, fusion);
    ensures Acyclic(k, s');
  {
    forall ref | ref in G.NewlyReachableReferences(s.bcv.view, s'.bcv.view, fusion.parentref)
      ensures ref in G.ReachableReferences(s.bcv.view, fusion.parentref)
      {
        var path :| G.NewPath(s.bcv.view, s'.bcv.view, fusion.parentref, path) && Last(path) == ref;
        if ref == path[1] {
          forall childref | childref in fusion.split_parent.children.Values
            ensures childref in fusion.fused_parent.children.Values + iset{fusion.left_childref, fusion.right_childref}
          {
            var key :| IMapsTo(fusion.split_parent.children, key, childref);
            if key in fusion.left_keys || key in fusion.right_keys {
            } else {
            }
          }
          assert fusion.split_parent.children.Values <= fusion.fused_parent.children.Values + iset{fusion.left_childref, fusion.right_childref}; // observe
          assert ref != fusion.left_childref; // observe
          assert ref != fusion.right_childref; // observe
          assert ref in fusion.fused_parent.children.Values; // observe
          assert G.IsPath(s.bcv.view, [fusion.parentref, ref]); // observe
        } else if path[|path|-2] == fusion.left_childref {
          assert path[|path|-3] == fusion.parentref || path[|path|-3] == fusion.left_childref || path[|path|-3] == fusion.right_childref;
          assert fusion.left_childref !in fusion.left_child.children.Values;
          assert fusion.left_childref !in fusion.right_child.children.Values;
          assert path[|path|-3] == fusion.parentref;
          assert fusion.left_childref in fusion.split_parent.children.Values;
          assert fusion.fused_childref in fusion.fused_parent.children.Values;
          assert G.IsPath(s.bcv.view, [fusion.parentref, fusion.fused_childref]); // observe
          assert G.IsPath(s.bcv.view, [fusion.fused_childref, ref]); // observe
          assert G.IsPath(s.bcv.view, [fusion.parentref, fusion.fused_childref, ref]); // observe
        } else {
          assert G.IsPath(s.bcv.view, [fusion.parentref, fusion.fused_childref, ref]); // observe
        }
      }
    G.LocalEditPreservesAcyclic(s.bcv.view, s'.bcv.view, fusion.parentref); // observe
    AcyclicGraphImpliesAcyclic(k, s'); // observe
  }

  lemma MergePreservesAcyclic(k: Constants, s: Variables, s': Variables, fusion: NodeFusion)
    requires Inv(k, s);
    requires Merge(k.bck, s.bcv, s'.bcv, fusion);
    ensures Acyclic(k, s');
  {
    forall ref | ref in G.NewlyReachableReferences(s.bcv.view, s'.bcv.view, fusion.parentref)
      ensures ref in G.ReachableReferences(s.bcv.view, fusion.parentref)
    {
      var path :| G.NewPath(s.bcv.view, s'.bcv.view, fusion.parentref, path) && Last(path) == ref;
      if ref == path[1] {
        forall childref | childref in fusion.fused_parent.children.Values
          ensures childref in fusion.split_parent.children.Values + iset{fusion.fused_childref}
        {
          var key :| IMapsTo(fusion.fused_parent.children, key, childref);
          if key in fusion.left_keys || key in fusion.right_keys {
          } else {
          }
        }
        assert fusion.fused_parent.children.Values <= fusion.split_parent.children.Values + iset{fusion.fused_childref};
        assert ref != fusion.fused_childref;
        assert ref in fusion.split_parent.children.Values;
        assert G.IsPath(s.bcv.view, [fusion.parentref, ref]);
      } else {
        assert path[|path|-2] == fusion.fused_childref;
        assert path[|path|-3] == fusion.parentref;
        assert
          || G.IsPath(s.bcv.view, [fusion.parentref, fusion.left_childref, ref])
          || G.IsPath(s.bcv.view, [fusion.parentref, fusion.right_childref, ref]);
      }
    }
    G.LocalEditPreservesAcyclic(s.bcv.view, s'.bcv.view, fusion.parentref); // observe
    AcyclicGraphImpliesAcyclic(k, s'); // observe
  }

  //
  // Preservation proofs
  //
  
  lemma GrowEquivalentLookups(k: Constants, s: Variables, s': Variables, oldroot: Node, newchildref: Reference)
  requires Inv(k, s)
  requires Grow(k.bck, s.bcv, s'.bcv, oldroot, newchildref)
  ensures EquivalentLookups(k, s, s')
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

    GrowPreservesAcyclic(k, s, s', oldroot, newchildref);
    
    forall lookup': Lookup, key, value | IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
    ensures exists lookup :: IsSatisfyingLookup(k, s.bcv.view, key, value, lookup)
    {
      if (|lookup'| == 1) {
		assert InterpretLookup(lookup', key) == G.M.Update(G.M.NopDelta());
        assert false;
      }

      // Remove one for the root
      assert |lookup'| >= 2;
      var lookup := [ReadOp(Root(), lookup'[1].node)] + lookup'[2..];

      InterpretLookupAdditive([ReadOp(Root(), lookup'[1].node)], lookup'[2..], key);
      InterpretLookupAdditive(lookup'[..2], lookup'[2..], key);
      assert lookup'[..2] + lookup'[2..] == lookup';

      forall i | 0 <= i < |lookup|-1
        ensures LookupFollowsChildRefAtLayer(key, lookup, i)
      {
        assert LookupFollowsChildRefAtLayer(key, lookup', i+1);
      }
      
      assert IsSatisfyingLookup(k, s.bcv.view, key, value, lookup);
    }
  }

  ////////
  //////// Flush
  ////////

  lemma FlushEquivalentLookups(k: Constants, s: Variables, s': Variables, parentref: Reference, parent: Node, childref: Reference, child: Node, newchildref: Reference, movedKeys: iset<Key>)
  requires Inv(k, s)
  requires Flush(k.bck, s.bcv, s'.bcv, parentref, parent, childref, child, newchildref, movedKeys)
  ensures EquivalentLookups(k, s, s')
  {
	//FIXME
	assume false;

    var newbuffer := imap k :: (if k in movedKeys then G.M.Merge(parent.buffer[k], child.buffer[k]) else child.buffer[k]);
    var newchild := Node(child.children, newbuffer);
    var newparentbuffer := imap k :: (if k in movedKeys then G.M.Update(G.M.NopDelta()) else parent.buffer[k]);
    var newparentchildren := imap k | k in parent.children :: (if k in movedKeys then newchildref else parent.children[k]);
    var newparent := Node(newparentchildren, newparentbuffer);

    forall lookup:Lookup, key, value | IsSatisfyingLookup(k, s.bcv.view, key, value, lookup)
      ensures exists lookup' :: IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
    {
	    if i :| 0 <= i < |lookup| && lookup[i].ref == parentref {
		    if key !in movedKeys {
			    var lookup' := lookup[i := ReadOp(parentref, newparent)];
			    forall j | 0 <= j < |lookup'|
			    ensures IMapsTo(s'.bcv.view, lookup'[j].ref, lookup'[j].node) {
			    }
			    assert lookup[..i] + [lookup[i]] + lookup[i+1..] == lookup; // observe
			    assert lookup'[..i] + [lookup'[i]] + lookup'[i+1..] == lookup'; // observe
			    InterpretLookupAdditive3(lookup[..i], [lookup[i]], lookup[i+1..], key);
			    InterpretLookupAdditive3(lookup'[..i], [lookup'[i]], lookup'[i+1..], key);
			    assert IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup'); // observe
		    } else {
			    if |lookup| - 1 == i { // we stopped at parent
				    var lookup' := lookup[..i] + [ ReadOp(parentref, newparent) ] + [ ReadOp(newchildref, newchild) ];
				    forall j | 0 <= j < |lookup'|
				    ensures IMapsTo(s'.bcv.view, lookup'[j].ref, lookup'[j].node) {
				    }
				    assert IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup'); // observe
			    } else {
				    var middle := [ lookup[i] ] + [ lookup[i+1] ];
				    var middle' := ([ ReadOp(parentref, newparent) ] + [ ReadOp(newchildref, newchild) ]);

				    assert lookup == lookup[..i] + middle + lookup[i+2..];
				    var lookup' := lookup[..i] + middle' + lookup[i+2..];

				    forall j | 0 <= j < |lookup'|
				    ensures IMapsTo(s'.bcv.view, lookup'[j].ref, lookup'[j].node) {
						if j == i {
						} else {
						}
				    }

				    assert lookup[..i] == lookup'[..i];
				    assert lookup[i+2..] == lookup'[i+2..];

				    assert InterpretLookup([lookup'[i]], key) == G.M.Update(G.M.NopDelta());

				    InterpretLookupAdditive3(lookup[..i], middle, lookup[i+2..], key);
				    InterpretLookupAdditive3(lookup'[..i], middle', lookup'[i+2..], key);

				    assert IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup'); // observe
			    }
		    }
	    } else {
		    assert IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup);
	    }
    }
    
	  FlushPreservesAcyclic(k, s, s', parentref, parent, childref, child, newchildref, movedKeys);
    
    forall lookup': Lookup, key, value | IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
      ensures exists lookup :: IsSatisfyingLookup(k, s.bcv.view, key, value, lookup)
    {
	    if i :| 0 <= i < |lookup'| && lookup'[i].ref == parentref {
	      if i < |lookup'| - 1 && lookup'[i+1].ref == newchildref {
          var middle' := [ lookup'[i] ] + [ lookup'[i+1] ];
          var middle := [ ReadOp(parentref, parent) ] + [ ReadOp(childref, child) ];
          var lookup := lookup'[..i] + middle + lookup'[i+2..];

          assert lookup' == lookup'[..i] + middle' + lookup'[i+2..];
          assert lookup == lookup[..i] + middle + lookup[i+2..];

          forall idx | 0 <= idx < |lookup|
            ensures IMapsTo(s.bcv.view, lookup[idx].ref, lookup[idx].node)
            {
              if idx == i {
                //assume false;
              } else if idx == i + 1 {
                //assume false;
              } else {
                assert lookup[idx].ref == lookup'[idx].ref;
                assert lookup'[idx].ref != parentref;
                assert lookup'[idx].ref != newchildref;
                assert s.bcv.view[lookup[idx].ref] == s'.bcv.view[lookup[idx].ref];
                assume false;
              }
            }
          assert IsPathFromRootLookup(k, s.bcv.view, key, lookup);
          assert LookupVisitsWFNodes(lookup);

          assert InterpretLookup([lookup'[i]], key) == G.M.Update(G.M.NopDelta());
          assert InterpretLookup(middle, key) == InterpretLookup(middle', key);

          assert lookup[..i] == lookup'[..i];
          assert lookup[i+2..] == lookup'[i+2..];
          
				  InterpretLookupAdditive3(lookup[..i], middle, lookup[i+2..], key);
				  InterpretLookupAdditive3(lookup'[..i], middle', lookup'[i+2..], key);

          
          assert IsSatisfyingLookup(k, s.bcv.view, key, value, lookup); // observe
          
	      } else {
			    var lookup := lookup'[i := ReadOp(parentref, parent)];
			    assert forall ref :: ref in s'.bcv.view && ref != parentref && ref != newchildref ==> s.bcv.view[ref] == s'.bcv.view[ref];
			    assert IMapsTo(s.bcv.view, parentref, parent);
			    if j :| 0 <= j < |lookup| && lookup[j].ref == newchildref {
				    assert j != 0;
				    assert lookup[j - 1].node.children[key] == newchildref;
			    }
			    assert LookupRespectsDisk(s.bcv.view, lookup);
			    assert lookup[..i] + [lookup[i]] + lookup[i+1..] == lookup; // observe
			    assert lookup'[..i] + [lookup'[i]] + lookup'[i+1..] == lookup'; // observe
			    InterpretLookupAdditive3(lookup[..i], [lookup[i]], lookup[i+1..], key);
			    InterpretLookupAdditive3(lookup'[..i], [lookup'[i]], lookup'[i+1..], key);
			    assert IsSatisfyingLookup(k, s.bcv.view, key, value, lookup); // observe
	      }
	    } else {
        if i :| 0 <= i < |lookup'| && lookup'[i].ref == newchildref {
          assert i != 0;
          assert newchildref in lookup'[i-1].node.children.Values;
          assert false;
        }
		    assert IsSatisfyingLookup(k, s.bcv.view, key, value, lookup');
	    }
      // var lookup := flushTransformLookupRev(lookup', key, parentref, parent, childref, child, newchildref);
      // FlushPreservesIsPathFromLookupRev(k, s, s', parentref, parent, childref, child, newchildref, lookup, lookup', key);

      //FIXME transformLookupParentAndChildPreservesAccumulatedLogRevPrefix(k, s, s', parentref, parent, childref, child, newchildref, movedKeys, lookup, lookup', key);
      //FIXME reveal_IsPrefix();

      //FIXME assert IsSatisfyingLookup(k, s.bcv.view, key, value, lookup);
    }
  }

  ////////
  //////// Split
  ////////

  lemma SplitParentIsWFNode(fusion: NodeFusion)
    requires WFNode(fusion.fused_parent)
    requires ValidSplit(fusion)
    ensures WFNode(fusion.split_parent)
  {
    forall key | key !in fusion.split_parent.children
      ensures BufferIsDefining(fusion.split_parent.buffer[key])
    {
      if key in fusion.left_keys {
      } else if key in fusion.right_keys {
      } else {
      }
    }
  }

  lemma SplitEquivalentLookups2(k: Constants, s: Variables, s': Variables, fusion: NodeFusion)
  requires Inv(k, s)
  requires Split(k.bck, s.bcv, s'.bcv, fusion);
  ensures EquivalentLookups(k, s, s');
  {
    SplitParentIsWFNode(fusion);
    
    forall lookup:Lookup, key, value | IsSatisfyingLookup(k, s.bcv.view, key, value, lookup)
      ensures exists lookup' :: IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
    {
      if i :| 0 <= i < |lookup| && lookup[i].ref == fusion.parentref {
        if key in fusion.left_keys + fusion.right_keys && i < |lookup| - 1 {
          var childref' := if key in fusion.left_keys then fusion.left_childref else fusion.right_childref;
          var child' := s'.bcv.view[childref'];
          var lookup' := lookup[i := G.ReadOp(fusion.parentref, fusion.split_parent)][i + 1 := G.ReadOp(childref', child')];

          forall j | 0 <= j < |lookup'|-1
            ensures LookupFollowsChildRefAtLayer(key, lookup', j)
          {
            if j == i {
            } else if j == i + 1 {
              assert LookupFollowsChildRefAtLayer(key, lookup, i);
              assert LookupFollowsChildRefAtLayer(key, lookup, j);
            } else {
              assert LookupFollowsChildRefAtLayer(key, lookup, j);
            }
          }

          var middle :=  [lookup[i]]  + [lookup[i+1]];
          var middle' := [lookup'[i]] + [lookup'[i+1]];

          assert lookup[i].node.buffer == lookup'[i].node.buffer;

          assert LookupFollowsChildRefAtLayer(key, lookup, i);
          assert lookup[i+1].node == fusion.fused_child;
          assert lookup[i+1].node.buffer[key] == lookup'[i+1].node.buffer[key];
          
          assert InterpretLookup(middle', key) == InterpretLookup(middle, key);          
          
          InterpretLookupAdditive3(lookup'[..i], middle', lookup'[i+2..], key);
          assert lookup' == lookup'[..i] + middle' + lookup'[i+2..];
          
          InterpretLookupAdditive3(lookup[..i], middle, lookup[i+2..], key);
          assert lookup == lookup[..i] + middle + lookup[i+2..];

          assert IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup');

        } else {
          var lookup' := lookup[i := G.ReadOp(fusion.parentref, fusion.split_parent)];
          
          forall j | 0 <= j < |lookup'|-1
            ensures LookupFollowsChildRefAtLayer(key, lookup', j)
          {
            assert LookupFollowsChildRefAtLayer(key, lookup, j);
          }

          InterpretLookupAdditive3(lookup'[..i], [lookup'[i]], lookup'[i+1..], key);
          assert lookup' == lookup'[..i] + [lookup'[i]] + lookup'[i+1..];
          
          InterpretLookupAdditive3(lookup[..i], [lookup[i]], lookup[i+1..], key);
          assert lookup == lookup[..i] + [lookup[i]] + lookup[i+1..];
          
          assert IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup');
        }
      } else {
        assert IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup);
      }
    }

    forall lookup': Lookup, key, value | IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
      ensures exists lookup :: IsSatisfyingLookup(k, s.bcv.view, key, value, lookup)
    {
      if i :| 0 <= i < |lookup'| && lookup'[i].ref == fusion.parentref {
        assume false;
      } else {
        // if j :| 0 <= j < |lookup'| && lookup'[j].ref == fusion.left_childref || lookup'[j].ref == fusion.right_childref {
        //   assert false;
        // }
        assert IsSatisfyingLookup(k, s.bcv.view, key, value, lookup');
      }
    }

  }
  
  // Define the transformations for splits:

  // These are the relations we should get out between lookup and lookup' if we obtain lookup'
  // by taking lookup and doing the following:
  //  - replace each instance of parentref/fused_parent with parentref/split_parent
  //  - replace each instance of fused_child with left_child (for left keys only, and only when directly after the parent in the lookup)
  //  - replace each instance of fused_child with left_child (for left keys only, and only when directly after the parent in the lookup)
  //  - leave everything else the same
  predicate SplitLookups(fusion: NodeFusion, lookup: Lookup, lookup': Lookup, key: Key)
  {
    && |lookup| == |lookup'|
    && |lookup| > 0

    // the lookup[i].ref == fusion.fused_childref condition is redundant for well-formed lookups
    && (key in fusion.left_keys ==> (
      && (forall i :: 0 < i < |lookup| && lookup[i-1].ref == fusion.parentref ==>
          lookup'[i].ref == fusion.left_childref)
      && (forall i :: 0 < i < |lookup| && lookup[i-1].ref == fusion.parentref ==>
          lookup'[i].node == fusion.left_child)
    ))

    && (key in fusion.right_keys ==> (
      && (forall i :: 0 < i < |lookup| && lookup[i-1].ref == fusion.parentref ==>
          lookup'[i].ref == fusion.right_childref)
      && (forall i :: 0 < i < |lookup| && lookup[i-1].ref == fusion.parentref ==>
          lookup'[i].node == fusion.right_child)
    ))

    && lookup'[0].ref == lookup[0].ref
    && (lookup[0].ref != fusion.parentref ==> lookup'[0].node == lookup[0].node)
    && (lookup[0].ref == fusion.parentref ==> lookup'[0].node == fusion.split_parent)

    && (forall i :: 0 < i < |lookup| && lookup[i-1].ref != fusion.parentref ==> lookup'[i].ref == lookup[i].ref)
    && (forall i :: 0 < i < |lookup| && lookup[i].ref != fusion.parentref && lookup[i-1].ref != fusion.parentref ==> lookup'[i].node == lookup[i].node)
    && (forall i :: 0 < i < |lookup| && lookup[i].ref == fusion.parentref && lookup[i-1].ref != fusion.parentref ==> lookup'[i].node == fusion.split_parent)

    && ((key !in fusion.left_keys && key !in fusion.right_keys) ==> (
      && (forall i :: 0 <= i < |lookup| ==> lookup'[i].ref == lookup[i].ref)
      && (forall i :: 0 <= i < |lookup| ==> lookup'[i].ref != fusion.parentref ==> lookup'[i].node == lookup[i].node)
      && (forall i :: 0 <= i < |lookup| ==> lookup'[i].ref == fusion.parentref ==> lookup'[i].node == fusion.split_parent)
    ))
  }

  function {:opaque} splitLookup(fusion: NodeFusion, lookup: Lookup, key: Key) : Lookup
  requires |lookup| > 0
  ensures |splitLookup(fusion, lookup, key)| == |lookup|
  {
    if (|lookup| == 1) then (
      var node := if lookup[0].ref == fusion.parentref then fusion.split_parent else lookup[0].node;
      [ReadOp(lookup[0].ref, node)]
    ) else (
      var pref := splitLookup(fusion, lookup[..|lookup|-1], key);
      var prevRef := lookup[|lookup| - 2].ref;
      var curRef := lookup[|lookup| - 1].ref;
      var curNode := lookup[|lookup| - 1].node;
      var ref := (if key in fusion.left_keys && prevRef == fusion.parentref then fusion.left_childref else
                 (if key in fusion.right_keys && prevRef == fusion.parentref then fusion.right_childref else
                 curRef));
      var node := (if key in fusion.left_keys && prevRef == fusion.parentref then fusion.left_child else
                 (if key in fusion.right_keys && prevRef == fusion.parentref then fusion.right_child else
                 (if ref == fusion.parentref then fusion.split_parent else
                 curNode)));
      pref + [ReadOp(ref, node)]
    )
  }

  lemma splitLookupProperties(fusion: NodeFusion, lookup: Lookup, lookup': Lookup, key: Key)
  requires |lookup| > 0
  requires ValidFusion(fusion);
  requires lookup' == splitLookup(fusion, lookup, key);
  ensures SplitLookups(fusion, lookup, lookup', key);
  {
    reveal_splitLookup();
    if (|lookup| == 1) {
      assert SplitLookups(fusion, lookup, lookup', key);
    } else {
      assert lookup'[..|lookup|-1] == splitLookup(fusion, lookup[..|lookup|-1], key);
      splitLookupProperties(fusion, lookup[..|lookup|-1], lookup'[..|lookup|-1], key);
      assert SplitLookups(fusion, lookup, lookup', key);
    }
  }

  lemma SplitLookupPreservesAccumulatedBuffer(k: Constants, s: Variables, s': Variables, fusion: NodeFusion, key: Key, lookup: Lookup, lookup': Lookup)
  requires |lookup| > 0;
  requires SplitLookups(fusion, lookup, lookup', key);
  requires Split(k.bck, s.bcv, s'.bcv, fusion);
  requires ValidFusion(fusion);
  requires IsPathFromRootLookup(k, s.bcv.view, key, lookup);
  requires IsPathFromRootLookup(k, s'.bcv.view, key, lookup');
  requires LookupVisitsWFNodes(lookup);
  requires LookupVisitsWFNodes(lookup');
  ensures InterpretLookup(lookup, key) == InterpretLookup(lookup', key);
  {
    if (|lookup| == 1) {
    } else {
      SplitLookupPreservesAccumulatedBuffer(k, s, s', fusion, key, lookup[..|lookup|-1], lookup'[..|lookup|-1]);
      assert Last(lookup).node.buffer[key] == Last(lookup').node.buffer[key];
    }
  }

  lemma SplitPreservesIsPathFromRootLookup(k: Constants, s: Variables, s': Variables, fusion: NodeFusion, lookup: Lookup, lookup': Lookup, key: Key)
  requires Inv(k, s);
  requires Split(k.bck, s.bcv, s'.bcv, fusion);
  requires SplitLookups(fusion, lookup, lookup', key)
  requires IsPathFromRootLookup(k, s.bcv.view, key, lookup);
  ensures IsPathFromRootLookup(k, s'.bcv.view, key, lookup');
  {
    /*
    var view' := s'.bcv.view;
    forall i | 0 <= i < |lookup'|
    ensures IMapsTo(view', lookup'[i].ref, lookup'[i].node)
    {
      if (i == 0) {
        if (lookup[i].ref == fusion.parentref) {
          assert IMapsTo(view', lookup'[i].ref, lookup'[i].node);
        } else {
          assert IMapsTo(view', lookup'[i].ref, lookup'[i].node);
        }
      } else {
        if (lookup[i-1].ref == fusion.parentref && key in fusion.left_keys) {
          assert IMapsTo(view', lookup'[i].ref, lookup'[i].node);
        }
        else if (lookup[i-1].ref == fusion.parentref && key in fusion.right_keys) {
          assert IMapsTo(view', lookup'[i].ref, lookup'[i].node);
        }
        else if (lookup[i].ref == fusion.parentref) {
          assert IMapsTo(view', lookup'[i].ref, lookup'[i].node);
        }
        else {
          assert IMapsTo(view', lookup'[i].ref, lookup'[i].node);
        }
      }
    }
    */
  }

  // Define the transformations for merges (reverse splits):

  // These are the relations we should get out between lookup and lookup' if we obtain lookup'
  // by taking lookup' and doing the following:
  //  - replace each instance of parentref/split_parent with parentref/fused_parent
  //  - replace each instance of left_child with fused_child (for left keys only, and only when directly after the parent in the lookup)
  //  - replace each instance of right_child with fused_child (for right keys only, and only when directly after the parent in the lookup)
  //  - leave everything else the same
  predicate MergeLookups(fusion: NodeFusion, lookup: Lookup, lookup': Lookup, key: Key)
  {
    && |lookup| == |lookup'|
    && |lookup'| > 0

    && (key in fusion.left_keys ==> (
      && (forall i :: 0 < i < |lookup'| && lookup'[i-1].ref == fusion.parentref ==>
          lookup[i].ref == fusion.fused_childref)
      && (forall i :: 0 < i < |lookup'| && lookup'[i-1].ref == fusion.parentref ==>
          lookup[i].node == fusion.fused_child)
    ))

    && (key in fusion.right_keys ==> (
      && (forall i :: 0 < i < |lookup'| && lookup'[i-1].ref == fusion.parentref ==>
          lookup[i].ref == fusion.fused_childref)
      && (forall i :: 0 < i < |lookup'| && lookup'[i-1].ref == fusion.parentref ==>
          lookup[i].node == fusion.fused_child)
    ))

    && lookup[0].ref == lookup'[0].ref
    && (lookup'[0].ref != fusion.parentref ==> lookup[0].node == lookup'[0].node)
    && (lookup'[0].ref == fusion.parentref ==> lookup[0].node == fusion.fused_parent)

    && (forall i :: 0 < i < |lookup'| && lookup'[i-1].ref != fusion.parentref ==> lookup[i].ref == lookup'[i].ref)
    && (forall i :: 0 < i < |lookup'| && lookup'[i].ref != fusion.parentref && lookup'[i-1].ref != fusion.parentref ==> lookup[i].node == lookup'[i].node)
    && (forall i :: 0 < i < |lookup'| && lookup'[i].ref == fusion.parentref && lookup'[i-1].ref != fusion.parentref ==> lookup[i].node == fusion.fused_parent)

    && ((key !in fusion.left_keys && key !in fusion.right_keys) ==> (
      && (forall i :: 0 <= i < |lookup'| ==> lookup[i].ref == lookup'[i].ref)
      && (forall i :: 0 <= i < |lookup'| ==> lookup[i].ref != fusion.parentref ==> lookup[i].node == lookup'[i].node)
      && (forall i :: 0 <= i < |lookup'| ==> lookup[i].ref == fusion.parentref ==> lookup[i].node == fusion.fused_parent)
    ))
  }

  function {:opaque} mergeLookup(fusion: NodeFusion, lookup': Lookup, key: Key) : Lookup
  requires |lookup'| > 0
  ensures |mergeLookup(fusion, lookup', key)| == |lookup'|
  {
    if (|lookup'| == 1) then (
      var node := if lookup'[0].ref == fusion.parentref then fusion.fused_parent else lookup'[0].node;
      [ReadOp(lookup'[0].ref, node)]
    ) else (
      var pref := mergeLookup(fusion, lookup'[..|lookup'|-1], key);
      var prevRef := lookup'[|lookup'| - 2].ref;
      var curRef := lookup'[|lookup'| - 1].ref;
      var curNode := lookup'[|lookup'| - 1].node;
      var ref := (if key in fusion.left_keys && prevRef == fusion.parentref then fusion.fused_childref else
                 (if key in fusion.right_keys && prevRef == fusion.parentref then fusion.fused_childref else
                 curRef));
      var node := (if key in fusion.left_keys && prevRef == fusion.parentref then fusion.fused_child else
                 (if key in fusion.right_keys && prevRef == fusion.parentref then fusion.fused_child else
                 (if ref == fusion.parentref then fusion.fused_parent else
                 curNode)));
      pref + [ReadOp(ref, node)]
    )
  }

  lemma mergeLookupProperties(fusion: NodeFusion, lookup: Lookup, lookup': Lookup, key: Key)
  requires |lookup'| > 0
  requires ValidFusion(fusion);
  requires lookup == mergeLookup(fusion, lookup', key);
  ensures MergeLookups(fusion, lookup, lookup', key);
  {
    reveal_mergeLookup();
    if (|lookup'| == 1) {
      assert MergeLookups(fusion, lookup, lookup', key);
    } else {
      assert lookup[..|lookup|-1] == mergeLookup(fusion, lookup'[..|lookup|-1], key);
      mergeLookupProperties(fusion, lookup[..|lookup|-1], lookup'[..|lookup|-1], key);
      assert MergeLookups(fusion, lookup, lookup', key);
    }
  }

  lemma MergeLookupPreservesAccumulatedBuffer(k: Constants, s: Variables, s': Variables, fusion: NodeFusion, key: Key, lookup: Lookup, lookup': Lookup)
    requires |lookup'| > 0;
    requires MergeLookups(fusion, lookup, lookup', key);
    requires Split(k.bck, s.bcv, s'.bcv, fusion);
    requires ValidFusion(fusion);
    requires IsPathFromRootLookup(k, s.bcv.view, key, lookup);
    requires IsPathFromRootLookup(k, s'.bcv.view, key, lookup');
    requires LookupVisitsWFNodes(lookup);
    requires LookupVisitsWFNodes(lookup');
    ensures InterpretLookup(lookup, key) == InterpretLookup(lookup', key);
    {
      if (|lookup'| == 1) {
      } else {
        MergeLookupPreservesAccumulatedBuffer(k, s, s', fusion, key, lookup[..|lookup|-1], lookup'[..|lookup|-1]);
        assert Last(lookup).node.buffer[key] == Last(lookup').node.buffer[key];
      }
    }

  lemma SplitPreservesIsPathFromRootLookupRev(k: Constants, s: Variables, s': Variables, fusion: NodeFusion, lookup: Lookup, lookup': Lookup, key: Key)
  requires Inv(k, s);
  requires Split(k.bck, s.bcv, s'.bcv, fusion);
  requires MergeLookups(fusion, lookup, lookup', key)
  requires IsPathFromRootLookup(k, s'.bcv.view, key, lookup');
  ensures IsPathFromRootLookup(k, s.bcv.view, key, lookup);
  {
    var view := s.bcv.view;

    if (|lookup'| == 0) {
    } else if (|lookup'| == 1) {
      if (lookup'[0].ref == fusion.parentref) {
        assert IMapsTo(view, lookup[0].ref, lookup[0].node);
      } else {
        assert lookup[0].ref == Root();
        assert lookup[0].node == lookup'[0].node;
        assert IMapsTo(view, lookup[0].ref, lookup[0].node);
      }

      assert IsPathFromRootLookup(k, s.bcv.view, key, lookup);
    } else {
      SplitPreservesIsPathFromRootLookupRev(k, s, s', fusion, lookup[..|lookup|-1], lookup'[..|lookup|-1], key);

      forall i | 0 <= i < |lookup|
      ensures IMapsTo(view, lookup[i].ref, lookup[i].node)
      {
        if (i == |lookup| - 1) {
          if (lookup'[i-1].ref == fusion.parentref && key in fusion.left_keys) {
            assert IMapsTo(view, lookup[i].ref, lookup[i].node);
          }
          else if (lookup'[i-1].ref == fusion.parentref && key in fusion.right_keys) {
            assert IMapsTo(view, lookup[i].ref, lookup[i].node);
          }
          else if (lookup'[i].ref == fusion.parentref) {
            assert IMapsTo(view, lookup[i].ref, lookup[i].node);
          }
          else {
            assert IMapsTo(view, lookup[i].ref, lookup[i].node);
          }
        } else {
          assert IMapsTo(view, lookup[i].ref, lookup[i].node);
        }
      }

      forall i | 0 <= i < |lookup| - 1
      ensures key in lookup[i].node.children
      ensures lookup[i].node.children[key] == lookup[i+1].ref
      {
        if (i == |lookup| - 2) {
          if (i > 0 && lookup'[i-1].ref == fusion.parentref && key in fusion.left_keys) {
            assert lookup[i].node.children[key] == lookup[i+1].ref;
          }
          else if (i > 0 && lookup'[i-1].ref == fusion.parentref && key in fusion.right_keys) {
            assert lookup[i].node.children[key] == lookup[i+1].ref;
          }
          else if (lookup'[i].ref == fusion.parentref) {
            assert lookup[i].node.children[key] == lookup[i+1].ref;
          }
          else {
            assert lookup[i].node.children[key] == lookup[i+1].ref;
          }
        } else {
          assert lookup[i].node.children[key] == lookup[i+1].ref;
        }
      }

      assert IsPathFromRootLookup(k, s.bcv.view, key, lookup);
    }
  }

  lemma SplitPreservesAcyclicLookup(k: Constants, s: Variables, s': Variables, fusion: NodeFusion, lookup': Lookup, key: Key)
  requires Inv(k, s)
  requires Split(k.bck, s.bcv, s'.bcv, fusion);
  requires IsPathFromRootLookup(k, s'.bcv.view, key, lookup')
  ensures LookupIsAcyclic(lookup')
  {
    var lookup := mergeLookup(fusion, lookup', key);
    mergeLookupProperties(fusion, lookup, lookup', key);
    SplitPreservesIsPathFromRootLookupRev(k, s, s', fusion, lookup, lookup', key);
    assert LookupIsAcyclic(lookup);
    forall i, j | 0 <= i < |lookup'| && 0 <= j < |lookup'| && i != j
    ensures lookup'[i].ref != lookup'[j].ref
    {
      if (lookup'[i].ref == lookup'[j].ref) {
        if (lookup'[i].ref == fusion.left_childref && key in fusion.left_keys) {
          assert i > 0;
          assert lookup'[i-1].ref == fusion.parentref;

          assert j > 0;
          assert lookup'[j-1].ref == fusion.parentref;

          assert lookup[i].ref == fusion.fused_childref;
          assert lookup[j].ref == fusion.fused_childref;
          assert false;
        } else if (lookup'[i].ref == fusion.right_childref && key in fusion.right_keys) {
          assert i > 0;
          assert lookup'[i-1].ref == fusion.parentref;

          assert j > 0;
          assert lookup'[j-1].ref == fusion.parentref;

          assert lookup[i].ref == fusion.fused_childref;
          assert lookup[j].ref == fusion.fused_childref;
          assert false;
        } else {
          assert lookup[i].ref == lookup'[i].ref;
          assert lookup[j].ref == lookup'[j].ref;
          assert false;
        }
      }
    }
  }

  lemma SplitPreservesAcyclicOld(k: Constants, s: Variables, s': Variables, fusion: NodeFusion)
  requires Inv(k, s);
  requires Split(k.bck, s.bcv, s'.bcv, fusion);
  ensures Acyclic(k, s');
  {
    forall key, lookup':Lookup | IsPathFromRootLookup(k, s'.bcv.view, key, lookup')
    ensures LookupIsAcyclic(lookup')
    {
      SplitPreservesAcyclicLookup(k, s, s', fusion, lookup', key);
    }
  }

  lemma SplitPreservesIsSatisfyingLookup(k: Constants, s: Variables, s': Variables, fusion: NodeFusion, lookup: Lookup, lookup': Lookup, key: Key, value: Value)
  requires Inv(k, s);
  requires Split(k.bck, s.bcv, s'.bcv, fusion);
  requires |lookup| > 0;
  requires lookup' == splitLookup(fusion, lookup, key)
  requires IsSatisfyingLookup(k, s.bcv.view, key, value, lookup);
  ensures IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup');
  {
    splitLookupProperties(fusion, lookup, lookup', key);
    SplitPreservesIsPathFromRootLookup(k, s, s', fusion, lookup, lookup', key);

    forall k | k !in fusion.split_parent.children
    ensures BufferIsDefining(fusion.split_parent.buffer[k])
    {
      assert k !in fusion.left_keys;
      assert k !in fusion.right_keys;
      assert k !in fusion.fused_parent.children;
    }
    assert WFNode(fusion.split_parent);

    assert WFNode(fusion.left_child);
    assert WFNode(fusion.right_child);
    
    SplitLookupPreservesAccumulatedBuffer(k, s, s', fusion, key, lookup, lookup');
  }

  lemma SplitPreservesIsSatisfyingLookupRev(k: Constants, s: Variables, s': Variables, fusion: NodeFusion, lookup: Lookup, lookup': Lookup, key: Key, value: Value)
  requires Inv(k, s);
  requires Split(k.bck, s.bcv, s'.bcv, fusion);
  requires |lookup'| > 0;
  requires lookup == mergeLookup(fusion, lookup', key)
  requires IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup');
  ensures IsSatisfyingLookup(k, s.bcv.view, key, value, lookup);
  {
    mergeLookupProperties(fusion, lookup, lookup', key);
    SplitPreservesIsPathFromRootLookupRev(k, s, s', fusion, lookup, lookup', key);

    MergeLookupPreservesAccumulatedBuffer(k, s, s', fusion, key, lookup, lookup');
  }

  lemma SplitEquivalentLookups(k: Constants, s: Variables, s': Variables, fusion: NodeFusion)
  requires Inv(k, s)
  requires Split(k.bck, s.bcv, s'.bcv, fusion);
  ensures EquivalentLookups(k, s, s');
  {
    forall lookup:Lookup, key, value | IsSatisfyingLookup(k, s.bcv.view, key, value, lookup)
    ensures exists lookup' :: IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
    {
      var lookup' := splitLookup(fusion, lookup, key);
      SplitPreservesIsSatisfyingLookup(k, s, s', fusion, lookup, lookup', key, value);
    }

    forall lookup': Lookup, key, value | IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
    ensures exists lookup :: IsSatisfyingLookup(k, s.bcv.view, key, value, lookup)
    {
      var lookup := mergeLookup(fusion, lookup', key);
      SplitPreservesIsSatisfyingLookupRev(k, s, s', fusion, lookup, lookup', key, value);
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
    ensures Acyclic(k, s')
  {
    forall key1, lookup': Lookup | IsPathFromRootLookup(k, s'.bcv.view, key1, lookup')
      ensures LookupIsAcyclic(lookup')
      ensures key1 in Last(lookup').node.children ==> Last(lookup').node.children[key1] in s'.bcv.view
    {
      var lookup := Apply((x: Layer) => x.(node := if x.ref in s.bcv.view then s.bcv.view[x.ref] else EmptyNode()), lookup');
      assert IsPathFromRootLookup(k, s.bcv.view, key1, lookup);
    }
  }

  lemma InsertMessagePreservesTotality(k: Constants, s: Variables, s': Variables, key: Key, msg: BufferEntry, oldroot: Node)
    requires Inv(k, s)
    requires InsertMessage(k.bck, s.bcv, s'.bcv, key, msg, oldroot)
    ensures forall key1 | MS.InDomain(key1) :: KeyHasSatisfyingLookup(k, s'.bcv.view, key1)
  {
    forall key1 | MS.InDomain(key1)
      ensures KeyHasSatisfyingLookup(k, s'.bcv.view, key1)
    {
      var value, lookup: Lookup :| IsSatisfyingLookup(k, s.bcv.view, key1, value, lookup);
      var lookup' := Apply((x: Layer) => x.(node := if x.ref in s'.bcv.view then s'.bcv.view[x.ref] else EmptyNode()),
                           lookup);
      if key1 != key {
        var i := 1;
        while i < |lookup|
        invariant i <= |lookup|
        invariant InterpretLookup(lookup'[..i], key1) == InterpretLookup(lookup[..i], key1);
        {
          assert lookup[..i] == lookup[..i+1][..i];
          assert lookup'[..i] == lookup'[..i+1][..i];
          i := i + 1;
        }
        assert lookup == lookup[..i];
        assert lookup' == lookup'[..i];
        assert InterpretLookup(lookup', key1) == InterpretLookup(lookup, key1);

        assert BufferDefinesValue(InterpretLookup(lookup', key1), value);
        assert IsSatisfyingLookup(k, s'.bcv.view, key1, value, lookup');
      } else {
		assert lookup' == [lookup'[0]] + lookup'[1..];
		InterpretLookupAdditive([lookup'[0]], lookup'[1..], key);
		assert lookup[1..] == lookup'[1..];
		G.M.MergeIsAssociative(msg, InterpretLookup([lookup[0]], key), InterpretLookup(lookup[1..], key));
		InterpretLookupAdditive([lookup[0]], lookup[1..], key);
		assert lookup == [lookup[0]] + lookup[1..];
		var message' := G.M.Merge(msg, InterpretLookup(lookup, key));
        assert IsSatisfyingLookup(k, s'.bcv.view, key1, message'.value, lookup');
      }
    }
  }
    
  lemma InsertMessageStepPreservesInvariant(k: Constants, s: Variables, s': Variables, key: Key, msg: BufferEntry, oldroot: Node)
    requires Inv(k, s)
    requires InsertMessage(k.bck, s.bcv, s'.bcv, key, msg, oldroot)
    ensures Inv(k, s')
  {
    InsertMessagePreservesAcyclicAndReachablePointersValid(k, s, s', key, msg, oldroot);
    InsertMessagePreservesTotality(k, s, s', key, msg, oldroot);
  }

  lemma FlushStepPreservesInvariant(k: Constants, s: Variables, s': Variables,
                                           parentref: Reference, parent: Node, childref: Reference, child: Node, newchildref: Reference, movedKeys: iset<Key>)
    requires Inv(k, s)
    requires Flush(k.bck, s.bcv, s'.bcv, parentref, parent, childref, child, newchildref, movedKeys)
    ensures Inv(k, s')
  {
    FlushPreservesAcyclic(k, s, s', parentref, parent, childref, child, newchildref, movedKeys);
    FlushEquivalentLookups(k, s, s', parentref, parent, childref, child, newchildref, movedKeys);
  }
  
  lemma GrowStepPreservesInvariant(k: Constants, s: Variables, s': Variables, oldroot: Node, newchildref: Reference)
    requires Inv(k, s)
    requires Grow(k.bck, s.bcv, s'.bcv, oldroot, newchildref)
    ensures Inv(k, s')
  {
    GrowPreservesAcyclic(k, s, s', oldroot, newchildref);
    GrowEquivalentLookups(k, s, s', oldroot, newchildref);
  }
 
  lemma SplitStepPreservesInvariant(k: Constants, s: Variables, s': Variables, fusion: NodeFusion)
    requires Inv(k, s)
    requires Split(k.bck, s.bcv, s'.bcv, fusion)
    ensures Inv(k, s')
  {
    SplitPreservesAcyclic(k, s, s', fusion);
    SplitEquivalentLookups(k, s, s', fusion);
    //SplitPreservesReachablePointersValid(k, s, s', fusion);
  }

  lemma MergeStepPreservesInvariant(k: Constants, s: Variables, s': Variables, fusion: NodeFusion)
    requires Inv(k, s)
    requires Merge(k.bck, s.bcv, s'.bcv, fusion)
    ensures Inv(k, s')
  {
	MergePreservesAcyclic(k, s, s', fusion);
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

  lemma GCStepPreservesIsPathFromRootLookupRev(k: Constants, s: Variables, s': Variables, refs: iset<Reference>, lookup: Lookup, key: Key)
    requires Inv(k, s)
    requires BI.GC(k.bck, s.bcv, s'.bcv, refs)
    requires IsPathFromRootLookup(k, s'.bcv.view, key, lookup);
    ensures IsPathFromRootLookup(k, s.bcv.view, key, lookup);
  {
  }

  lemma GCStepPreservesAcyclicity(k: Constants, s: Variables, s': Variables, refs: iset<Reference>)
    requires Inv(k, s)
    requires BI.GC(k.bck, s.bcv, s'.bcv, refs)
    ensures Acyclic(k, s')
  {
    forall key, lookup | IsPathFromRootLookup(k, s'.bcv.view, key, lookup)
    ensures LookupIsAcyclic(lookup)
    {
      GCStepPreservesIsPathFromRootLookupRev(k, s, s', refs, lookup, key);
    }
  }

  lemma GCStepEquivalentLookups(k: Constants, s: Variables, s': Variables, refs: iset<Reference>)
    requires Inv(k, s)
    requires BI.GC(k.bck, s.bcv, s'.bcv, refs)
    ensures EquivalentLookups(k, s, s')
  {
    forall lookup:Lookup, key, value | IsSatisfyingLookup(k, s.bcv.view, key, value, lookup)
    ensures exists lookup' :: IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
    {
      GCStepPreservesIsPathFromRootLookup(k, s, s', refs, lookup, key);
      assert IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup);
    }

    forall lookup': Lookup, key, value | IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
    ensures exists lookup :: IsSatisfyingLookup(k, s.bcv.view, key, value, lookup)
    {
      GCStepPreservesIsPathFromRootLookupRev(k, s, s', refs, lookup', key);
      assert IsSatisfyingLookup(k, s.bcv.view, key, value, lookup');
    }
  }

  lemma GCStepPreservesInvariant(k: Constants, s: Variables, s': Variables, refs: iset<Reference>)
    requires Inv(k, s)
    requires BI.GC(k.bck, s.bcv, s'.bcv, refs)
    ensures Inv(k, s')
  {
    BI.GCPreservesInv(k.bck, s.bcv, s'.bcv, refs);
    GCStepPreservesAcyclicity(k, s, s', refs);
    GCStepEquivalentLookups(k, s, s', refs);
  }

  // Putting it all together

  lemma BetreeStepPreservesInvariant(k: Constants, s: Variables, s': Variables, uiop: UIOp, betreeStep: BetreeStep)
    requires Inv(k, s)
    requires Betree(k, s, s', uiop, betreeStep)
    ensures Inv(k, s')
  {
    match betreeStep {
      case BetreeQuery(q) => QueryStepPreservesInvariant(k, s, s');
      case BetreeInsert(ins) => InsertMessageStepPreservesInvariant(k, s, s', ins.key, ins.msg, ins.oldroot);
      case BetreeFlush(flush) => FlushStepPreservesInvariant(k, s, s', flush.parentref, flush.parent, flush.childref, flush.child, flush.newchildref, flush.movedKeys);
      case BetreeGrow(growth) => GrowStepPreservesInvariant(k, s, s', growth.oldroot, growth.newchildref);
      case BetreeSplit(fusion) => SplitStepPreservesInvariant(k, s, s', fusion);
      case BetreeMerge(fusion) => MergeStepPreservesInvariant(k, s, s', fusion);
    }
  }

  lemma NextStepPreservesInvariant(k: Constants, s: Variables, s': Variables, uiop: UIOp, step: Step)
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
  
  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp)
    requires Inv(k, s)
    requires Next(k, s, s', uiop)
    ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', uiop, step);
    NextStepPreservesInvariant(k, s, s', uiop, step);
  }
}
