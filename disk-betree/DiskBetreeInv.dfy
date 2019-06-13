include "../lib/Maps.dfy"
include "../lib/sequences.dfy"
include "MapSpec.dfy"
include "DiskBetree.dfy"
  
abstract module DiskBetreeInv {
  import opened DB : DiskBetree
  import opened Maps
  import opened Sequences

  predicate KeyHasSatisfyingLookup<Value(!new)>(k: Constants, view: BI.View<Node>, key: Key)
  {
    exists lookup, value :: IsSatisfyingLookup(k, view, key, value, lookup)
  }

  predicate LookupIsAcyclic(lookup: Lookup) {
    forall i, j :: 0 <= i < |lookup| && 0 <= j < |lookup| && i != j ==> lookup[i].ref != lookup[j].ref
  }
  
  predicate Acyclic<Value(!new)>(k: Constants, s: Variables) {
    forall key, lookup ::
      IsPathFromRootLookup(k, s.bcv.view, key, lookup) ==>
      LookupIsAcyclic(lookup)
  }

  predicate ReachablePointersValid<Value(!new)>(k: Constants, s: Variables) {
    forall key, lookup: Lookup<Value> ::
      IsPathFromRootLookup(k, s.bcv.view, key, lookup) && key in lookup[|lookup|-1].node.children ==>
      lookup[|lookup|-1].node.children[key] in s.bcv.view
  }
  
  predicate Inv(k: Constants, s: Variables)
  {
    && BI.Inv(k.bck, s.bcv)
    && (forall key | MS.InDomain(key) :: KeyHasSatisfyingLookup(k, s.bcv.view, key))
    && Acyclic(k, s)
    && ReachablePointersValid(k, s)
  }

  //// Definitions for lookup preservation

  // One-way preservation

  predicate PreservesLookups<Value(!new)>(k: Constants, s: Variables, s': Variables)
  {
    forall lookup, key, value :: IsSatisfyingLookup(k, s.bcv.view, key, value, lookup) ==>
      exists lookup' :: IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
  }

  predicate PreservesLookupsExcept<Value(!new)>(k: Constants, s: Variables, s': Variables, exceptQuery: Key)
  {
    forall lookup, key, value :: key != exceptQuery && IsSatisfyingLookup(k, s.bcv.view, key, value, lookup) ==>
      exists lookup' :: IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
  }

  // Two-way preservation

  predicate EquivalentLookups<Value(!new)>(k: Constants, s: Variables, s': Variables)
  {
    && PreservesLookups(k, s, s')
    && PreservesLookups(k, s', s)
  }

  predicate EquivalentLookupsWithPut<Value(!new)>(k: Constants, s: Variables, s': Variables, key: Key, value: Value)
  {
    && PreservesLookupsExcept(k, s, s', key)
    && PreservesLookupsExcept(k, s', s, key)
    && exists lookup :: IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup)
  }

  // CantEquivocate
  // It's a lemma here (follows from structure of Lookups) - not an invariant!

  lemma SatisfyingLookupsForKeyAgree<Value>(k: Constants, s: Variables, key: Key, value: Value, value': Value, lookup: Lookup, lookup': Lookup, idx: int)
  requires IsSatisfyingLookup(k, s.bcv.view, key, value, lookup);
  requires IsSatisfyingLookup(k, s.bcv.view, key, value', lookup');
  requires 0 <= idx < |lookup|;
  requires 0 <= idx < |lookup'|;
  ensures lookup[idx] == lookup'[idx];
  {
    if (idx == 0) {
    } else {
      SatisfyingLookupsForKeyAgree(k, s, key, value, value', lookup, lookup', idx - 1);
    }
  }

  lemma LongerLookupDefinesSameValue<Value>(k: Constants, s: Variables, key: Key, value: Value, lookup: Lookup, idx1: int, idx2: int, value': Value)
  requires 0 <= idx1 <= idx2 < |lookup|;
  requires BufferDefinesValue(lookup[idx1].accumulatedBuffer, value);
  requires IsSatisfyingLookup(k, s.bcv.view, key, value', lookup);
  ensures BufferDefinesValue(lookup[idx2].accumulatedBuffer, value);
  decreases idx2;
  {
    if (idx1 == idx2) {
    } else {
      LongerLookupDefinesSameValue(k, s, key, value, lookup, idx1, idx2 - 1, value');
    }
  }

  lemma CantEquivocateWlog<Value>(k: Constants, s: Variables, key: Key, value: Value, value': Value, lookup: Lookup, lookup': Lookup)
  requires IsSatisfyingLookup(k, s.bcv.view, key, value, lookup);
  requires IsSatisfyingLookup(k, s.bcv.view, key, value', lookup');
  requires |lookup| <= |lookup'|
  ensures value == value';
  {
    var idx := |lookup| - 1;
    SatisfyingLookupsForKeyAgree(k, s, key, value, value', lookup, lookup', idx);
    assert BufferDefinesValue(lookup[idx].accumulatedBuffer, value);
    assert BufferDefinesValue(lookup'[idx].accumulatedBuffer, value);
    LongerLookupDefinesSameValue(k, s, key, value, lookup', idx, |lookup'| - 1, value');
  }

  lemma CantEquivocate<Value>(k: Constants, s: Variables, key: Key, value: Value, value': Value, lookup: Lookup, lookup': Lookup)
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

  ////////
  //////// Grow
  ////////

  // Acyclicity proofs

  lemma GrowPreservesAcyclicLookup(k: Constants, s: Variables, s': Variables, oldroot: Node, newchildref: BI.Reference, key: Key, lookup': Lookup)
    requires Inv(k, s)
    requires Grow(k, s, s', oldroot, newchildref)
    requires IsPathFromRootLookup(k, s'.bcv.view, key, lookup')
    ensures LookupIsAcyclic(lookup')
    decreases lookup'
  {
    if (|lookup'| <= 2) {
    } else {
      // var lookup := lookup'[1..][0 := Layer(BI.Root(k.bck), lookup'[1].node, lookup'[1].accumulatedBuffer)];
      // assert s'.bcv.view.Keys == s'.bcv.view.Keys + iset{newchildref};
      // assert forall i :: 0 <= i < |lookup| ==> lookup[i].ref in s.bcv.view;
      // assert IsPathFromRootLookup(k, s.bcv.view, key, lookup);
      
      var sublookup' := lookup'[ .. |lookup'| - 1];
      GrowPreservesAcyclicLookup(k, s, s', oldroot, newchildref, key, sublookup');
      var sublookup := sublookup'[1..][0 := Layer(BI.Root(k.bck), sublookup'[1].node, sublookup'[1].accumulatedBuffer)];
      assert s'.bcv.view[newchildref] == oldroot;
      assert sublookup'[1].node == oldroot;
      assert IMapsTo(s.bcv.view, BI.Root(k.bck), sublookup'[1].node);
      assert IsPathFromRootLookup(k, s.bcv.view, key, sublookup);
      var lastLayer := lookup'[|lookup'| - 1];

      assert lastLayer.ref in s.bcv.view;

      var lookup := sublookup + [Layer(lastLayer.ref, s.bcv.view[lastLayer.ref], [])];

      assert IMapsTo(s.bcv.view, lookup[|lookup|-1].ref, lookup[|lookup|-1].node);

      assert IsPathFromRootLookup(k, s.bcv.view, key, lookup);
      assert LookupIsAcyclic(lookup);

      forall i, j | 0 <= i < |lookup'| && 0 <= j < |lookup'| && i != j
      ensures lookup'[i].ref != lookup'[j].ref
      {
        if (i == 0) {
          if (j == 1) {
            assert lookup'[i].ref != lookup'[j].ref;
          } else {
            assert lookup'[i].ref == BI.Root(k.bck);
            assert lookup'[j].ref == lookup[j-1].ref;
            assert lookup[j-1].ref != lookup[0].ref;
            assert lookup'[j].ref != BI.Root(k.bck);
            assert lookup'[i].ref != lookup'[j].ref;
          }
        } else if (i == 1) {
          if (j == 0) {
            assert lookup'[i].ref != lookup'[j].ref;
          } else {
            assert lookup'[i].ref != lookup'[j].ref;
          }
        } else {
          if (j == 0) {
            assert lookup'[j].ref == BI.Root(k.bck);
            assert lookup'[i].ref == lookup[i-1].ref;
            assert lookup[i-1].ref != lookup[0].ref;
            assert lookup'[i].ref != BI.Root(k.bck);

            assert lookup'[i].ref != lookup'[j].ref;
          } else if (j == 1) {
            assert lookup'[i].ref != lookup'[j].ref;
          } else {
            assert lookup[i-1].ref != lookup[j-1].ref;
            assert lookup'[i].ref != lookup'[j].ref;
          }
        }
      }

      assert LookupIsAcyclic(lookup');
    }
  }

  lemma GrowPreservesAcyclic(k: Constants, s: Variables, s': Variables, oldroot: Node, newchildref: BI.Reference)
    requires Inv(k, s)
    requires Grow(k, s, s', oldroot, newchildref)
    ensures Acyclic(k, s')
  {
    forall key, lookup' | IsPathFromRootLookup(k, s'.bcv.view, key, lookup')
    ensures LookupIsAcyclic(lookup')
    {
      GrowPreservesAcyclicLookup(k, s, s', oldroot, newchildref, key, lookup');
    }
  }

  lemma GrowPreservesReachablePointersValid(k: Constants, s: Variables, s': Variables, oldroot: Node, newchildref: BI.Reference)
    requires Inv(k, s)
    requires Grow(k, s, s', oldroot, newchildref)
    ensures ReachablePointersValid(k, s')
  {
    forall key, lookup':Lookup | 
      IsPathFromRootLookup(k, s'.bcv.view, key, lookup') && key in lookup'[|lookup'|-1].node.children
    ensures lookup'[|lookup'|-1].node.children[key] in s'.bcv.view
    {
      if (|lookup'| == 1) {
        assert lookup'[|lookup'|-1].node.children[key] in s'.bcv.view;
      } else {
        var lookup := lookup'[1..][0 := Layer(BI.Root(k.bck), lookup'[1].node, lookup'[1].accumulatedBuffer)];
        GrowPreservesAcyclic(k, s, s', oldroot, newchildref);
        assert IsPathFromRootLookup(k, s.bcv.view, key, lookup);
        assert lookup[|lookup|-1].node.children[key] in s.bcv.view;
        assert lookup'[|lookup'|-1].node.children[key] in s'.bcv.view;
      }
    }
  }

  // Preservation proofs
  
  lemma GrowEquivalentLookups(k: Constants, s: Variables, s': Variables, oldroot: Node, newchildref: BI.Reference)
  requires Inv(k, s)
  requires Grow(k, s, s', oldroot, newchildref)
  ensures EquivalentLookups(k, s, s')
  {
    forall lookup:Lookup, key, value | IsSatisfyingLookup(k, s.bcv.view, key, value, lookup)
    ensures exists lookup' :: IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
    {
      // Add one for the new root
      var rootref := BI.Root(k.bck);

      var newroot := s'.bcv.view[rootref];

      //assert LookupIsAcyclic(lookup);

      var lookup' := [
        Layer(rootref, newroot, []),
        Layer(newchildref, oldroot, lookup[0].accumulatedBuffer)
      ] + lookup[1..];

      assert IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup');
    }

    GrowPreservesAcyclic(k, s, s', oldroot, newchildref);
    
    forall lookup': Lookup, key, value | IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
    ensures exists lookup :: IsSatisfyingLookup(k, s.bcv.view, key, value, lookup)
    {
      // Remove one for the root
      var lookup := lookup'[1..][0 := Layer(BI.Root(k.bck), lookup'[1].node, lookup'[1].accumulatedBuffer)];
      assert IsSatisfyingLookup(k, s.bcv.view, key, value, lookup);
    }
  }

  ////////
  //////// Flush
  ////////

  // Definitions of Flush lookup transformations:

  function transformLookup<Value>(lookup: Lookup<Value>, key: Key, oldref: BI.Reference, newref: BI.Reference, newnode: Node) : Lookup<Value>
  ensures |transformLookup(lookup, key, oldref, newref, newnode)| == |lookup|;
  ensures forall i :: 0 <= i < |lookup| ==>
      transformLookup(lookup, key, oldref, newref, newnode)[i].ref ==
        (if lookup[i].ref == oldref then newref else lookup[i].ref);
  ensures forall i :: 0 <= i < |lookup| ==>
      transformLookup(lookup, key, oldref, newref, newnode)[i].node ==
        (if lookup[i].ref == oldref then newnode else lookup[i].node);
  //ensures |lookup| > 0 ==> transformLookup(lookup, key, oldref, newref, newnode)[0].accumulatedBuffer == transformLookup(lookup, key, oldref, newref, newnode)[0].node.buffer[key]
  //ensures (forall i :: 0 < i < |transformLookup(lookup, key, oldref, newref, newnode)| ==> transformLookup(lookup, key, oldref, newref, newnode)[i].accumulatedBuffer == transformLookup(lookup, key, oldref, newref, newnode)[i-1].accumulatedBuffer + transformLookup(lookup, key, oldref, newref, newnode)[i].node.buffer[key])
  decreases lookup
  {
    if |lookup| == 0 then
      []
    else
      var pref := transformLookup(lookup[.. |lookup| - 1], key, oldref, newref, newnode);
      var accBuf := if |pref| == 0 then [] else pref[|pref| - 1].accumulatedBuffer;
      pref +
        [if lookup[|lookup| - 1].ref == oldref then
          Layer(newref, newnode, accBuf + (if key in newnode.buffer then newnode.buffer[key] else []))
         else
          Layer(lookup[|lookup| - 1].ref, lookup[|lookup| - 1].node, accBuf + (if key in lookup[|lookup| - 1].node.buffer then lookup[|lookup| - 1].node.buffer[key] else []))
        ]
  }

  lemma transformLookupAccumulatesMessages<Value>(lookup: Lookup<Value>, key: Key, oldref: BI.Reference, newref: BI.Reference, newnode: Node)
  requires |lookup| > 0
  requires LookupVisitsWFNodes(transformLookup(lookup, key, oldref, newref, newnode))
  ensures LookupAccumulatesMessages(key, transformLookup(lookup, key, oldref, newref, newnode))
  {
  }

  // Change every parentref in lookup to the newparent, and likewise for the child.
  // However, when changing the child, we check first that it actually came from the parent
  // (since there might be other pointers to child)
  function transformLookupParentAndChild<Value>(lookup: Lookup<Value>, key: Key, parentref: BI.Reference, newparent: Node, movedKeys: iset<Key>, oldchildref: BI.Reference, newchildref: BI.Reference, newchild: Node) : Lookup<Value>
  requires |lookup| > 0
  ensures |transformLookupParentAndChild(lookup, key, parentref, newparent, movedKeys, oldchildref, newchildref, newchild)| == |lookup|;
  decreases lookup
  {
    var pref := if |lookup| > 1 then transformLookupParentAndChild(lookup[.. |lookup| - 1], key, parentref, newparent, movedKeys, oldchildref, newchildref, newchild) else [];

    var accBuf := if |pref| == 0 then [] else pref[|pref| - 1].accumulatedBuffer;
    var lastLayer := Last(lookup);
    var ref := 
      (if lastLayer.ref == parentref then parentref else
       if lastLayer.ref == oldchildref && |lookup| > 1 && lookup[|lookup|-2].ref == parentref && key in movedKeys then newchildref else
       lastLayer.ref);
    var node :=
      (if lastLayer.ref == parentref then newparent else
       if lastLayer.ref == oldchildref && |lookup| > 1 && lookup[|lookup|-2].ref == parentref && key in movedKeys then newchild else

       lastLayer.node);
    pref + [Layer(ref, node, accBuf + (if key in node.buffer then node.buffer[key] else []))]
  }

  lemma transformLookupParentAndChildLemma<Value>(lookup: Lookup<Value>, lookup': Lookup<Value>, key: Key, parentref: BI.Reference, newparent: Node, movedKeys: iset<Key>, oldchildref: BI.Reference, newchildref: BI.Reference, newchild: Node, i: int)
  requires 0 <= i < |lookup|
  requires lookup' == transformLookupParentAndChild(lookup, key, parentref, newparent, movedKeys, oldchildref, newchildref, newchild)
  ensures
    lookup'[i].ref ==
        (if lookup[i].ref == parentref then parentref else
         if lookup[i].ref == oldchildref && i > 0 && lookup[i-1].ref == parentref && key in movedKeys then newchildref else
         lookup[i].ref)
  ensures
    lookup'[i].node ==
        (if lookup[i].ref == parentref then newparent else
         if lookup[i].ref == oldchildref && i > 0 && lookup[i-1].ref == parentref && key in movedKeys then newchild else
         lookup[i].node)
  decreases |lookup|
  {
    if (i == |lookup| - 1) {
    } else {
      transformLookupParentAndChildLemma<Value>(lookup[..|lookup|-1], lookup'[..|lookup|-1],
          key, parentref, newparent, movedKeys, oldchildref, newchildref, newchild, i);
    }
  }

  lemma transformLookupParentAndChildAccumulatesMessages<Value>(lookup: Lookup<Value>, key: Key, parentref: BI.Reference, newparent: Node, movedKeys: iset<Key>, oldchildref: BI.Reference, newchildref: BI.Reference, newchild: Node)
  requires |lookup| > 0
  requires LookupVisitsWFNodes(transformLookupParentAndChild(lookup, key, parentref, newparent, movedKeys, oldchildref, newchildref, newchild));
  ensures LookupAccumulatesMessages(key, transformLookupParentAndChild(lookup, key, parentref, newparent, movedKeys, oldchildref, newchildref, newchild));
  {
    var lookup' := transformLookupParentAndChild(lookup, key, parentref, newparent, movedKeys, oldchildref, newchildref, newchild);
    if (|lookup| == 1) {
    } else {
      assert transformLookupParentAndChild(lookup[..|lookup|-1], key, parentref, newparent, movedKeys, oldchildref, newchildref, newchild) ==
          transformLookupParentAndChild(lookup, key, parentref, newparent, movedKeys, oldchildref, newchildref, newchild)[..|lookup|-1];
      assert LookupVisitsWFNodes(transformLookupParentAndChild(lookup[..|lookup|-1], key, parentref, newparent, movedKeys, oldchildref, newchildref, newchild));

      transformLookupParentAndChildAccumulatesMessages<Value>(lookup[..|lookup|-1], key, parentref, newparent, movedKeys, oldchildref, newchildref, newchild);

      assert LookupAccumulatesMessages(key, lookup');
    }
  }

  lemma transformLookupParentAndChildPreservesAccumulatedLog<Value>(
    k: Constants,
    s: Variables,
    s': Variables,
    lookup: Lookup<Value>,
    lookup': Lookup<Value>,
    key: Key,
    parent: Node,
    child: Node,
    parentref: BI.Reference,
    newparent: Node,
    movedKeys: iset<Key>,
    childref: BI.Reference,
    newchildref: BI.Reference,
    newchild: Node,
    newbuffer: Buffer,
    newparentbuffer: Buffer,
    newparentchildren: imap<Key, BI.Reference>)
  requires IsPathFromRootLookup(k, s.bcv.view, key, lookup);
  requires LookupAccumulatesMessages(key, lookup);
  requires LookupAccumulatesMessages(key, lookup');
  requires Flush(k, s, s', parentref, parent, childref, child, newchildref)
  requires movedKeys == iset k | k in parent.children && parent.children[k] == childref;
  requires newbuffer == imap k :: (if k in movedKeys then parent.buffer[k] + child.buffer[k] else child.buffer[k]);
  requires newchild == Node(child.children, newbuffer);
  requires newparentbuffer == imap k :: (if k in movedKeys then [] else parent.buffer[k]);
  requires newparentchildren == imap k | k in parent.children :: (if k in movedKeys then newchildref else parent.children[k]);
  requires newparent == Node(newparentchildren, newparentbuffer);

  requires |lookup| > 0
  requires key in movedKeys ==> IMapsTo(parent.children, key, childref);
  requires key in movedKeys ==> Last(lookup).ref != parentref

  requires lookup' == transformLookupParentAndChild(lookup, key, parentref, newparent, movedKeys, childref, newchildref, newchild)

  ensures Last(lookup').accumulatedBuffer == Last(lookup).accumulatedBuffer
  {
    if (|lookup| == 1) {
      if (lookup[0].ref == parentref) {
        assert !(key in movedKeys);
        assert Last(lookup').accumulatedBuffer
            == lookup'[0].node.buffer[key]
            == lookup[0].node.buffer[key]
            == Last(lookup).accumulatedBuffer;
      } else {
        assert Last(lookup').accumulatedBuffer
            == lookup'[0].node.buffer[key]
            == lookup[0].node.buffer[key]
            == Last(lookup).accumulatedBuffer;
      }
    } else {
      if (key in movedKeys && lookup[|lookup|-2].ref == parentref) {
        if (|lookup| == 2) {
          assert Last(lookup').accumulatedBuffer == Last(lookup).accumulatedBuffer;
        } else {
          assert lookup[|lookup|-2].node == parent;
          assert lookup[|lookup|-1].ref == childref;

          assert lookup[..|lookup|-1][..|lookup|-2] == lookup[..|lookup|-2];
          assert lookup'[..|lookup|-2]
              == transformLookupParentAndChild(lookup[..|lookup|-1], key, parentref, newparent, movedKeys, childref, newchildref, newchild)[..|lookup|-2]
              == transformLookupParentAndChild(lookup[..|lookup|-1][..|lookup|-2], key, parentref, newparent, movedKeys, childref, newchildref, newchild)
              == transformLookupParentAndChild(lookup[..|lookup|-2], key, parentref, newparent, movedKeys, childref, newchildref, newchild);

          transformLookupParentAndChildPreservesAccumulatedLog(k, s, s', lookup[..|lookup|-2], lookup'[..|lookup|-2], key, parent, child, parentref, newparent, movedKeys, childref, newchildref, newchild, newbuffer, newparentbuffer, newparentchildren);
          assert Last(lookup').accumulatedBuffer == Last(lookup).accumulatedBuffer;
        }
      } else {
        transformLookupParentAndChildPreservesAccumulatedLog(k, s, s', lookup[..|lookup|-1], lookup'[..|lookup|-1], key, parent, child, parentref, newparent, movedKeys, childref, newchildref, newchild, newbuffer, newparentbuffer, newparentchildren);
        assert Last(lookup').accumulatedBuffer == Last(lookup).accumulatedBuffer;
      }
    }
  }

  function flushTransformLookup<Value>(lookup: Lookup, key: Key, parentref: BI.Reference, parent: Node, childref: BI.Reference, child: Node, newchildref: BI.Reference) : Lookup
  requires |lookup| > 0
  requires WFNode(parent)
  requires WFNode(child)
  {
    var movedKeys := iset k | k in parent.children && parent.children[k] == childref;
    var newbuffer := imap k :: (if k in movedKeys then parent.buffer[k] + child.buffer[k] else child.buffer[k]);
    var newchild := Node(child.children, newbuffer);
    var newparentbuffer := imap k :: (if k in movedKeys then [] else parent.buffer[k]);
    var newparentchildren := imap k | k in parent.children :: (if k in movedKeys then newchildref else parent.children[k]);
    var newparent := Node(newparentchildren, newparentbuffer);
    var lookup1 := if Last(lookup).ref == parentref && key in movedKeys then lookup + [Layer(newchildref, newchild, Last(lookup).accumulatedBuffer + newchild.buffer[key])] else lookup;
    transformLookupParentAndChild(lookup1, key, parentref, newparent, movedKeys, childref, newchildref, newchild)
  }

  function flushTransformLookupRev<Value>(lookup': Lookup, key: Key, parentref: BI.Reference, parent: Node, childref: BI.Reference, child: Node, newchildref: BI.Reference) : Lookup
  {
    // TODO Use transformLookupParentAndChild instead?
    // This works fine, but only because newchildref is fresh.
    // This pattern doesn't work going the other way, so might as well change this one too
    // for more symmetry.
    transformLookup(transformLookup(lookup', key, newchildref, childref, child), key, parentref, parentref, parent)
  }

  lemma FlushPreservesIsPathFromLookupRev(k: Constants, s: Variables, s': Variables, parentref: BI.Reference, parent: Node, childref: BI.Reference, child: Node, newchildref: BI.Reference, lookup: Lookup, lookup': Lookup, key: Key)
  requires Inv(k, s)
  requires Flush(k, s, s', parentref, parent, childref, child, newchildref)
  requires IsPathFromRootLookup(k, s'.bcv.view, key, lookup')
  requires lookup == flushTransformLookupRev(lookup', key, parentref, parent, childref, child, newchildref);
  ensures IsPathFromRootLookup(k, s.bcv.view, key, lookup);
  // These follow immediately from IsPathFromRootLookup:
  //ensures LookupIsAcyclic(lookup);
  //ensures key in Last(lookup).node.children ==> Last(lookup).node.children[key] in s.bcv.view;
  decreases lookup'
  {
    if (|lookup'| == 0) {
    } else if (|lookup'| == 1) {
      assert BI.Root(k.bck) in s.bcv.view;
      assert lookup[0].node == s.bcv.view[BI.Root(k.bck)];
      assert IsPathFromRootLookup(k, s.bcv.view, key, lookup);
    } else {
      FlushPreservesIsPathFromLookupRev(k, s, s', parentref, parent, childref, child, newchildref,
        flushTransformLookupRev(lookup'[.. |lookup'| - 1], key, parentref, parent, childref, child, newchildref),
        lookup'[.. |lookup'| - 1], key);

      assert IsPathFromRootLookup(k, s.bcv.view, key, lookup);
    }
  }

  lemma FlushPreservesAcyclicLookup(k: Constants, s: Variables, s': Variables, parentref: BI.Reference, parent: Node, childref: BI.Reference, child: Node, newchildref: BI.Reference, lookup': Lookup, key: Key)
  requires Inv(k, s)
  requires Flush(k, s, s', parentref, parent, childref, child, newchildref)
  requires IsPathFromRootLookup(k, s'.bcv.view, key, lookup')
  ensures LookupIsAcyclic(lookup')
  {
    var movedKeys := iset k | k in parent.children && parent.children[k] == childref;
    var newbuffer := imap k :: (if k in movedKeys then parent.buffer[k] + child.buffer[k] else child.buffer[k]);
    var newparentbuffer := imap k :: (if k in movedKeys then [] else parent.buffer[k]);
    var newparentchildren := imap k | k in parent.children :: (if k in movedKeys then newchildref else parent.children[k]);
    var newparent := Node(newparentchildren, newparentbuffer);

    if (|lookup'| <= 1) {
    } else {
      var lookup := flushTransformLookupRev(lookup', key, parentref, parent, childref, child, newchildref);
      FlushPreservesIsPathFromLookupRev(k, s, s', parentref, parent, childref, child, newchildref, lookup, lookup', key);
    }
  }

  lemma FlushPreservesAcyclic(k: Constants, s: Variables, s': Variables, parentref: BI.Reference, parent: Node, childref: BI.Reference, child: Node, newchildref: BI.Reference)
    requires Inv(k, s)
    requires Flush(k, s, s', parentref, parent, childref, child, newchildref)
    ensures Acyclic(k, s')
  {
    forall key, lookup':Lookup | IsPathFromRootLookup(k, s'.bcv.view, key, lookup')
    ensures LookupIsAcyclic(lookup')
    {
      FlushPreservesAcyclicLookup(k, s, s', parentref, parent, childref, child, newchildref, lookup', key);
    }
  }


  lemma transformLookupParentAndChildPreservesAccumulatedLogRev<Value>(
    k: Constants,
    s: Variables,
    s': Variables,
    parentref: BI.Reference,
    parent: Node,
    childref: BI.Reference,
    child: Node,
    newchildref: BI.Reference,
    movedKeys: iset<Key>,
    lookup: Lookup<Value>,
    lookup': Lookup<Value>,
    key: Key
  )
  requires Inv(k, s)
  requires IsPathFromRootLookup(k, s.bcv.view, key, lookup);
  requires IsPathFromRootLookup(k, s'.bcv.view, key, lookup');
  requires LookupAccumulatesMessages(key, lookup);
  requires LookupAccumulatesMessages(key, lookup');
  requires Flush(k, s, s', parentref, parent, childref, child, newchildref)
  requires lookup == flushTransformLookupRev(lookup', key, parentref, parent, childref, child, newchildref)
  requires movedKeys == iset k | k in parent.children && parent.children[k] == childref;
  requires key in movedKeys ==> Last(lookup').ref != parentref
  ensures Last(lookup').accumulatedBuffer == Last(lookup).accumulatedBuffer
  {
    var newbuffer := imap k :: (if k in movedKeys then parent.buffer[k] + child.buffer[k] else child.buffer[k]);
    var newchild := Node(child.children, newbuffer);
    var newparentbuffer := imap k :: (if k in movedKeys then [] else parent.buffer[k]);
    var newparentchildren := imap k | k in parent.children :: (if k in movedKeys then newchildref else parent.children[k]);
    var newparent := Node(newparentchildren, newparentbuffer);

    if (|lookup| == 1) {
      assert Last(lookup').accumulatedBuffer == Last(lookup).accumulatedBuffer;
    } else {
      if (key in movedKeys && Last(lookup').ref == newchildref) {
        if (|lookup| == 2) {
          assert lookup'[1].node == newchild;
          assert lookup'[0].ref == parentref;
          assert lookup'[0].node == newparent;
          assert Last(lookup').accumulatedBuffer
              == lookup[0].node.buffer[key] + lookup[1].node.buffer[key]
              == Last(lookup).accumulatedBuffer;
        } else {
          assert lookup'[..|lookup|-1][..|lookup|-2] == lookup'[..|lookup|-2];
          assert lookup[..|lookup|-2]
              == flushTransformLookupRev(lookup'[..|lookup|-1], key, parentref, parent, childref, child, newchildref)[..|lookup|-2]
              == flushTransformLookupRev(lookup'[..|lookup|-1][..|lookup|-2], key, parentref, parent, childref, child, newchildref)
              == flushTransformLookupRev(lookup'[..|lookup|-2], key, parentref, parent, childref, child, newchildref);

          transformLookupParentAndChildPreservesAccumulatedLogRev(k, s, s', parentref, parent, childref, child, newchildref, movedKeys, lookup[..|lookup|-2], lookup'[..|lookup|-2], key);
          assert Last(lookup').accumulatedBuffer == Last(lookup).accumulatedBuffer;
        }
      } else {
        transformLookupParentAndChildPreservesAccumulatedLogRev(k, s, s', parentref, parent, childref, child, newchildref, movedKeys, lookup[..|lookup|-1], lookup'[..|lookup|-1], key);
        assert Last(lookup').accumulatedBuffer == Last(lookup).accumulatedBuffer;
      }
    }
  }

  lemma transformLookupParentAndChildPreservesAccumulatedLogRevPrefix<Value>(
    k: Constants,
    s: Variables,
    s': Variables,
    parentref: BI.Reference,
    parent: Node,
    childref: BI.Reference,
    child: Node,
    newchildref: BI.Reference,
    movedKeys: iset<Key>,
    lookup: Lookup<Value>,
    lookup': Lookup<Value>,
    key: Key
  )
  requires Inv(k, s)
  requires IsPathFromRootLookup(k, s.bcv.view, key, lookup);
  requires IsPathFromRootLookup(k, s'.bcv.view, key, lookup');
  requires LookupAccumulatesMessages(key, lookup);
  requires LookupAccumulatesMessages(key, lookup');
  requires Flush(k, s, s', parentref, parent, childref, child, newchildref)
  requires lookup == flushTransformLookupRev(lookup', key, parentref, parent, childref, child, newchildref)
  requires movedKeys == iset k | k in parent.children && parent.children[k] == childref;
  ensures IsPrefix(Last(lookup').accumulatedBuffer, Last(lookup).accumulatedBuffer);
  {
    if (key in movedKeys && Last(lookup').ref == parentref) {
      var newbuffer := imap k :: (if k in movedKeys then parent.buffer[k] + child.buffer[k] else child.buffer[k]);
      var newchild := Node(child.children, newbuffer);

      var lookup1 := lookup + [Layer(childref, child, Last(lookup).accumulatedBuffer + child.buffer[key])];
      var lookup1' := lookup' + [Layer(newchildref, newchild, Last(lookup').accumulatedBuffer + newchild.buffer[key])];

      assert IsPathFromRootLookup(k, s.bcv.view, key, lookup1);
      assert IsPathFromRootLookup(k, s'.bcv.view, key, lookup1');

      transformLookupParentAndChildPreservesAccumulatedLogRev(
          k, s, s', parentref, parent, childref, child, newchildref, movedKeys, lookup1, lookup1', key);


      assert Last(lookup).accumulatedBuffer + child.buffer[key] == Last(lookup').accumulatedBuffer + newchild.buffer[key];

      reveal_IsSuffix();
      assert IsSuffix(child.buffer[key], newchild.buffer[key]);
      IsPrefixFromEqSums(Last(lookup).accumulatedBuffer, child.buffer[key], Last(lookup').accumulatedBuffer, newchild.buffer[key]);
    } else {
      transformLookupParentAndChildPreservesAccumulatedLogRev(
          k, s, s', parentref, parent, childref, child, newchildref, movedKeys, lookup, lookup', key);
      SelfIsPrefix(Last(lookup').accumulatedBuffer);
    }
  }

  lemma FlushEquivalentLookups(k: Constants, s: Variables, s': Variables, parentref: BI.Reference, parent: Node, childref: BI.Reference, child: Node, newchildref: BI.Reference)
  requires Inv(k, s)
  requires Flush(k, s, s', parentref, parent, childref, child, newchildref)
  ensures EquivalentLookups(k, s, s')
  {
    var movedKeys := iset k | k in parent.children && parent.children[k] == childref;
    var newbuffer := imap k :: (if k in movedKeys then parent.buffer[k] + child.buffer[k] else child.buffer[k]);
    var newchild := Node(child.children, newbuffer);
    var newparentbuffer := imap k :: (if k in movedKeys then [] else parent.buffer[k]);
    var newparentchildren := imap k | k in parent.children :: (if k in movedKeys then newchildref else parent.children[k]);
    var newparent := Node(newparentchildren, newparentbuffer);

    forall lookup:Lookup, key, value | IsSatisfyingLookup(k, s.bcv.view, key, value, lookup)
    ensures exists lookup' :: IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
    {
      var lookup1 := if Last(lookup).ref == parentref && key in movedKeys then lookup + [Layer(childref, child, Last(lookup).accumulatedBuffer + child.buffer[key])] else lookup;

      assert IsPathFromRootLookup(k, s.bcv.view, key, lookup1);

      var lookup' := flushTransformLookup(lookup, key, parentref, parent, childref, child, newchildref);

      transformLookupParentAndChildLemma(lookup1, lookup', key, parentref, newparent, movedKeys, childref, newchildref, newchild, 0);

      assert lookup'[0].ref == BI.Root(k.bck);

      forall i | 0 <= i < |lookup'|
      ensures IMapsTo(s'.bcv.view, lookup'[i].ref, lookup'[i].node)
      ensures WFNode(lookup'[i].node)
      {
        transformLookupParentAndChildLemma(lookup1, lookup', key, parentref, newparent, movedKeys, childref, newchildref, newchild, i);
      }

      forall i | 0 <= i < |lookup'| - 1
      ensures key in lookup'[i].node.children
      ensures lookup'[i].node.children[key] == lookup'[i+1].ref
      {
        transformLookupParentAndChildLemma(lookup1, lookup', key, parentref, newparent, movedKeys, childref, newchildref, newchild, i);
        transformLookupParentAndChildLemma(lookup1, lookup', key, parentref, newparent, movedKeys, childref, newchildref, newchild, i+1);
      }

      transformLookupParentAndChildAccumulatesMessages(lookup1, key, parentref, newparent, movedKeys, childref, newchildref, newchild);

      transformLookupParentAndChildPreservesAccumulatedLog(k, s, s', lookup1, lookup',
          key, parent, child, parentref, newparent, movedKeys, childref, newchildref,
          newchild, newbuffer, newparentbuffer, newparentchildren);

      assert IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup');
    }

    forall lookup': Lookup, key, value | IsSatisfyingLookup(k, s'.bcv.view, key, value, lookup')
    ensures exists lookup :: IsSatisfyingLookup(k, s.bcv.view, key, value, lookup)
    {
      var lookup := flushTransformLookupRev(lookup', key, parentref, parent, childref, child, newchildref);
      FlushPreservesIsPathFromLookupRev(k, s, s', parentref, parent, childref, child, newchildref, lookup, lookup', key);
      transformLookupAccumulatesMessages(transformLookup(lookup', key, newchildref, childref, child), key, parentref, parentref, parent);

      transformLookupParentAndChildPreservesAccumulatedLogRevPrefix(k, s, s', parentref, parent, childref, child, newchildref, movedKeys, lookup, lookup', key);
      reveal_IsPrefix();

      assert IsSatisfyingLookup(k, s.bcv.view, key, value, lookup);
    }
  }

  lemma FlushPreservesReachablePointersValid<Value>(k: Constants, s: Variables, s': Variables, parentref: BI.Reference, parent: Node, childref: BI.Reference, child: Node, newchildref: BI.Reference)
  requires Inv(k, s)
  requires Flush(k, s, s', parentref, parent, childref, child, newchildref)
  ensures ReachablePointersValid(k, s')
  {
    forall key, lookup': Lookup<Value> | IsPathFromRootLookup(k, s'.bcv.view, key, lookup') && key in lookup'[|lookup'|-1].node.children
    ensures 
      lookup'[|lookup'|-1].node.children[key] in s'.bcv.view
    {
      var lookup := flushTransformLookupRev(lookup', key, parentref, parent, childref, child, newchildref);
      FlushPreservesIsPathFromLookupRev(k, s, s', parentref, parent, childref, child, newchildref, lookup, lookup', key);
    }
  }

  ////////
  //////// Split
  ////////

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

    //&& (forall i :: 0 <= i < |lookup| && lookup[i].ref == fusion.parentref ==> lookup'[i].ref == fusion.parentref)
    //&& (forall i :: 0 <= i < |lookup| && lookup[i].ref == fusion.parentref ==> lookup'[i].node == fusion.split_parent)

    //&& (forall i :: 0 <= i < |lookup| && lookup'[i].ref == fusion.parentref ==> lookup[i].ref == fusion.parentref)
    //&& (forall i :: 0 <= i < |lookup| && lookup'[i].ref == fusion.parentref ==> lookup[i].node == fusion.fused_parent)

    // the lookup[i].ref == fusion.fused_childref condition is redundant for well-formed lookups
    && (key in fusion.left_keys ==> (
      && (forall i :: 0 < i < |lookup| && lookup[i-1].ref == fusion.parentref ==> // && lookup[i].ref == fusion.fused_childref ==>
          lookup'[i].ref == fusion.left_childref)
      && (forall i :: 0 < i < |lookup| && lookup[i-1].ref == fusion.parentref ==> //&& lookup[i].ref == fusion.fused_childref ==>
          lookup'[i].node == fusion.left_child)
    ))

    && (key in fusion.right_keys ==> (
      && (forall i :: 0 < i < |lookup| && lookup[i-1].ref == fusion.parentref ==> //&& lookup[i].ref == fusion.fused_childref ==>
          lookup'[i].ref == fusion.right_childref)
      && (forall i :: 0 < i < |lookup| && lookup[i-1].ref == fusion.parentref ==> //&& lookup[i].ref == fusion.fused_childref ==>
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
      [Layer(lookup[0].ref, node, (if key in node.buffer then node.buffer[key] else []))]
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
      pref + [Layer(ref, node, pref[|pref|-1].accumulatedBuffer + (if key in node.buffer then node.buffer[key] else []))]
    )
  }

  lemma splitLookupProperties<Value>(fusion: NodeFusion, lookup: Lookup, lookup': Lookup, key: Key)
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

  lemma SplitPreservesIsPathFromRootLookup(k: Constants, s: Variables, s': Variables, fusion: NodeFusion, lookup: Lookup, lookup': Lookup, key: Key)
  requires Inv(k, s);
  requires Split(k, s, s', fusion);
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

  ////////
  //////// Invariant proofs
  ////////

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
    assert forall key :: MS.InDomain(key) ==> IsSatisfyingLookup(k, s.bcv.view, key, MS.EmptyValue(), [Layer(BI.Root(k.bck), EmptyNode(), [Insertion(MS.EmptyValue())])]);
  }

  lemma QueryStepPreservesInvariant<Value>(k: Constants, s: Variables, s': Variables, key: Key, value: Value, lookup: Lookup)
    requires Inv(k, s)
    requires Query(k, s, s', key, value, lookup)
    ensures Inv(k, s')
  {
  }

  lemma InsertMessagePreservesAcyclicAndReachablePointersValid(k: Constants, s: Variables, s': Variables, key: Key, msg: BufferEntry, oldroot: Node)
    requires Inv(k, s)
    requires InsertMessage(k, s, s', key, msg, oldroot)
    ensures Acyclic(k, s')
    ensures ReachablePointersValid(k, s')
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
    requires InsertMessage(k, s, s', key, msg, oldroot)
    ensures forall key1 | MS.InDomain(key1) :: KeyHasSatisfyingLookup(k, s'.bcv.view, key1)
  {
    forall key1 | MS.InDomain(key1)
      ensures KeyHasSatisfyingLookup(k, s'.bcv.view, key1)
    {
      var value, lookup :| IsSatisfyingLookup(k, s.bcv.view, key1, value, lookup);
      var lookup' := Apply((x: Layer) => x.(node := if x.ref in s'.bcv.view then s'.bcv.view[x.ref] else EmptyNode(),
                                          accumulatedBuffer := (if key1 == key then [msg] else []) + x.accumulatedBuffer),
                           lookup);
      if key1 != key {
        assert IsSatisfyingLookup(k, s'.bcv.view, key1, value, lookup');
      } else {
        assert IsSatisfyingLookup(k, s'.bcv.view, key1, msg.value, lookup');
      }
    }
  }
    
  lemma InsertMessageStepPreservesInvariant<Value>(k: Constants, s: Variables, s': Variables, key: Key, msg: BufferEntry, oldroot: Node)
    requires Inv(k, s)
    requires InsertMessage(k, s, s', key, msg, oldroot)
    ensures Inv(k, s')
  {
    InsertMessagePreservesAcyclicAndReachablePointersValid(k, s, s', key, msg, oldroot);
    InsertMessagePreservesTotality(k, s, s', key, msg, oldroot);
  }

  lemma FlushStepPreservesInvariant<Value>(k: Constants, s: Variables, s': Variables,
                                           parentref: BI.Reference, parent: Node, childref: BI.Reference, child: Node, newchildref: BI.Reference)
    requires Inv(k, s)
    requires Flush(k, s, s', parentref, parent, childref, child, newchildref)
    ensures Inv(k, s')
  {
    FlushPreservesAcyclic(k, s, s', parentref, parent, childref, child, newchildref);
    FlushEquivalentLookups(k, s, s', parentref, parent, childref, child, newchildref);
    FlushPreservesReachablePointersValid(k, s, s', parentref, parent, childref, child, newchildref);
  }
  
  lemma GrowStepPreservesInvariant<Value>(k: Constants, s: Variables, s': Variables, oldroot: Node, newchildref: BI.Reference)
    requires Inv(k, s)
    requires Grow(k, s, s', oldroot, newchildref)
    ensures Inv(k, s')
  {
    GrowPreservesAcyclic(k, s, s', oldroot, newchildref);
    GrowEquivalentLookups(k, s, s', oldroot, newchildref);
    GrowPreservesReachablePointersValid(k, s, s', oldroot, newchildref);
  }

  lemma NextStepPreservesInvariant(k: Constants, s: Variables, s': Variables, step: Step)
    requires Inv(k, s)
    requires NextStep(k, s, s', step)
    ensures Inv(k, s')
  {
    match step {
      case QueryStep(key, value, lookup) => QueryStepPreservesInvariant(k, s, s', key, value, lookup);
      case InsertMessageStep(key, value, oldroot) => InsertMessageStepPreservesInvariant(k, s, s', key, value, oldroot);
      case FlushStep(parentref, parent, childref, child, newchildref) => FlushStepPreservesInvariant(k, s, s', parentref, parent, childref, child, newchildref);
      case GrowStep(oldroot, newchildref) => GrowStepPreservesInvariant(k, s, s', oldroot, newchildref);
    }
  }
  
  lemma NextPreservesInvariant(k: Constants, s: Variables, s': Variables)
    requires Inv(k, s)
    requires Next(k, s, s')
    ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', step);
    NextStepPreservesInvariant(k, s, s', step);
  }
    

}
