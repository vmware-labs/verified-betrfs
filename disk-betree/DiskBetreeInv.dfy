include "../lib/map_utils.dfy"
include "../lib/sequences.dfy"
include "MapSpec.dfy"
include "DiskBetree.dfy"
  
abstract module DiskBetreeInv {
  import opened DB : DiskBetree
  import opened Map_Utils
  import opened Sequences

  predicate KeyHasSatisfyingLookup<Value(!new)>(k: Constants, view: BC.View<Node>, key: Key)
  {
    exists lookup, value :: IsSatisfyingLookup(k, view, key, value, lookup)
  }

  predicate LookupIsAcyclic(lookup: Lookup) {
    forall i, j :: 0 <= i < |lookup| && 0 <= j < |lookup| && i != j ==> lookup[i].ref != lookup[j].ref
  }
  
  predicate Acyclic<Value(!new)>(k: Constants, s: Variables) {
    forall key, lookup ::
      IsPathFromRootLookup(k, BC.ViewOf(k.bck, s.bcv), key, lookup) ==>
      LookupIsAcyclic(lookup)
  }

  predicate ReachablePointersValid<Value(!new)>(k: Constants, s: Variables) {
    forall key, lookup: Lookup<Value> ::
      IsPathFromRootLookup(k, BC.ViewOf(k.bck, s.bcv), key, lookup) && key in lookup[|lookup|-1].node.children ==>
      lookup[|lookup|-1].node.children[key] in BC.ViewOf(k.bck, s.bcv)
  }
  
  predicate Inv(k: Constants, s: Variables)
  {
    && (forall key | MS.InDomain(key) :: KeyHasSatisfyingLookup(k, BC.ViewOf(k.bck, s.bcv), key))
    && Acyclic(k, s)
    && ReachablePointersValid(k, s)
  }

  //// Definitions for lookup preservation

  // One-way preservation

  predicate PreservesLookups<Value(!new)>(k: Constants, s: Variables, s': Variables)
  {
    forall lookup, key, value :: IsSatisfyingLookup(k, BC.ViewOf(k.bck, s.bcv), key, value, lookup) ==>
      exists lookup' :: IsSatisfyingLookup(k, BC.ViewOf(k.bck, s'.bcv), key, value, lookup')
  }

  predicate PreservesLookupsExcept<Value(!new)>(k: Constants, s: Variables, s': Variables, exceptQuery: Key)
  {
    forall lookup, key, value :: key != exceptQuery && IsSatisfyingLookup(k, BC.ViewOf(k.bck, s.bcv), key, value, lookup) ==>
      exists lookup' :: IsSatisfyingLookup(k, BC.ViewOf(k.bck, s'.bcv), key, value, lookup')
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
    && exists lookup :: IsSatisfyingLookup(k, BC.ViewOf(k.bck, s'.bcv), key, value, lookup)
  }

  // CantEquivocate
  // It's a lemma here (follows from structure of Lookups) - not an invariant!

  lemma SatisfyingLookupsForKeyAgree<Value>(k: Constants, s: Variables, key: Key, value: Value, value': Value, lookup: Lookup, lookup': Lookup, idx: int)
  requires IsSatisfyingLookup(k, BC.ViewOf(k.bck, s.bcv), key, value, lookup);
  requires IsSatisfyingLookup(k, BC.ViewOf(k.bck, s.bcv), key, value', lookup');
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
  requires IsSatisfyingLookup(k, BC.ViewOf(k.bck, s.bcv), key, value', lookup);
  ensures BufferDefinesValue(lookup[idx2].accumulatedBuffer, value);
  decreases idx2;
  {
    if (idx1 == idx2) {
    } else {
      LongerLookupDefinesSameValue(k, s, key, value, lookup, idx1, idx2 - 1, value');
    }
  }

  lemma CantEquivocateWlog<Value>(k: Constants, s: Variables, key: Key, value: Value, value': Value, lookup: Lookup, lookup': Lookup)
  requires IsSatisfyingLookup(k, BC.ViewOf(k.bck, s.bcv), key, value, lookup);
  requires IsSatisfyingLookup(k, BC.ViewOf(k.bck, s.bcv), key, value', lookup');
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
  requires IsSatisfyingLookup(k, BC.ViewOf(k.bck, s.bcv), key, value, lookup);
  requires IsSatisfyingLookup(k, BC.ViewOf(k.bck, s.bcv), key, value', lookup');
  ensures value == value';
  {
    if (|lookup| <= |lookup'|) {
      CantEquivocateWlog(k, s, key, value, value', lookup, lookup');
    } else {
      CantEquivocateWlog(k, s, key, value', value, lookup', lookup);
    }
  }

  // Acyclicity proofs

  lemma GrowPreservesAcyclicLookup(k: Constants, s: Variables, s': Variables, oldroot: Node, newchildref: BC.Reference, key: Key, lookup': Lookup)
    requires Inv(k, s)
    requires Grow(k, s, s', oldroot, newchildref)
    requires IsPathFromRootLookup(k, BC.ViewOf(k.bck, s'.bcv), key, lookup')
    ensures LookupIsAcyclic(lookup')
    decreases lookup'
  {
    if (|lookup'| <= 2) {
    } else {
      var sublookup' := lookup'[ .. |lookup'| - 1];
      GrowPreservesAcyclicLookup(k, s, s', oldroot, newchildref, key, sublookup');
      var sublookup := sublookup'[1..][0 := Layer(BC.Root(k.bck), sublookup'[1].node, sublookup'[1].accumulatedBuffer)];
      assert IsPathFromRootLookup(k, BC.ViewOf(k.bck, s.bcv), key, sublookup);
      var lastLayer := lookup'[|lookup'| - 1];

      assert lastLayer.ref in BC.ViewOf(k.bck, s.bcv);

      var lookup := sublookup + [Layer(lastLayer.ref, BC.ViewOf(k.bck, s.bcv)[lastLayer.ref], [])];

      assert IMapsTo(BC.ViewOf(k.bck, s.bcv), lookup[|lookup|-1].ref, lookup[|lookup|-1].node);

      assert IsPathFromRootLookup(k, BC.ViewOf(k.bck, s.bcv), key, lookup);
      assert LookupIsAcyclic(lookup);

      forall i, j | 0 <= i < |lookup'| && 0 <= j < |lookup'| && i != j
      ensures lookup'[i].ref != lookup'[j].ref
      {
        if (i == 0) {
          if (j == 1) {
            assert lookup'[i].ref != lookup'[j].ref;
          } else {
            assert lookup'[i].ref == BC.Root(k.bck);
            assert lookup'[j].ref == lookup[j-1].ref;
            assert lookup[j-1].ref != lookup[0].ref;
            assert lookup'[j].ref != BC.Root(k.bck);
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

  lemma GrowPreservesAcyclic(k: Constants, s: Variables, s': Variables, oldroot: Node, newchildref: BC.Reference)
    requires Inv(k, s)
    requires Grow(k, s, s', oldroot, newchildref)
    ensures Acyclic(k, s')
  {
    forall key, lookup' | IsPathFromRootLookup(k, BC.ViewOf(k.bck, s'.bcv), key, lookup')
    ensures LookupIsAcyclic(lookup')
    {
      GrowPreservesAcyclicLookup(k, s, s', oldroot, newchildref, key, lookup');
    }
  }

  lemma GrowPreservesReachablePointersValid(k: Constants, s: Variables, s': Variables, oldroot: Node, newchildref: BC.Reference)
    requires Inv(k, s)
    requires Grow(k, s, s', oldroot, newchildref)
    ensures ReachablePointersValid(k, s')
  {
    forall key, lookup':Lookup | 
      IsPathFromRootLookup(k, BC.ViewOf(k.bck, s'.bcv), key, lookup') && key in lookup'[|lookup'|-1].node.children
    ensures lookup'[|lookup'|-1].node.children[key] in BC.ViewOf(k.bck, s'.bcv)
    {
      if (|lookup'| == 1) {
        assert lookup'[|lookup'|-1].node.children[key] in BC.ViewOf(k.bck, s'.bcv);
      } else {
        var lookup := lookup'[1..][0 := Layer(BC.Root(k.bck), lookup'[1].node, lookup'[1].accumulatedBuffer)];
        GrowPreservesAcyclic(k, s, s', oldroot, newchildref);
        assert IsPathFromRootLookup(k, BC.ViewOf(k.bck, s.bcv), key, lookup);
        assert lookup[|lookup|-1].node.children[key] in BC.ViewOf(k.bck, s.bcv);
        assert lookup'[|lookup'|-1].node.children[key] in BC.ViewOf(k.bck, s'.bcv);
      }
    }
  }

  function transformLookup<Value>(lookup: Lookup<Value>, oldref: BC.Reference, newref: BC.Reference, newnode: Node) : Lookup<Value>
  ensures |transformLookup(lookup, oldref, newref, newnode)| == |lookup|
  ensures forall i :: 0 <= i < |lookup| ==>
      transformLookup(lookup, oldref, newref, newnode)[i].ref ==
        (if lookup[i].ref == oldref then newref else lookup[i].ref)
  ensures forall i :: 0 <= i < |lookup| ==>
      transformLookup(lookup, oldref, newref, newnode)[i].node ==
        (if lookup[i].ref == oldref then newnode else lookup[i].node)
  decreases lookup
  {
    if |lookup| == 0 then
      []
    else
      transformLookup(lookup[.. |lookup| - 1], oldref, newref, newnode) + 
        [if lookup[|lookup| - 1].ref == oldref then Layer(newref, newnode, lookup[|lookup|-1].accumulatedBuffer) else lookup[|lookup| - 1]]
  }

  function flushTransformLookupRev<Value>(lookup': Lookup, parentref: BC.Reference, parent: Node, childref: BC.Reference, child: Node, newchildref: BC.Reference) : Lookup
  {
    transformLookup(transformLookup(lookup', newchildref, childref, child), parentref, parentref, parent)
  }

  lemma FlushPreservesIsPathFromLookupRev(k: Constants, s: Variables, s': Variables, parentref: BC.Reference, parent: Node, childref: BC.Reference, child: Node, newchildref: BC.Reference, lookup: Lookup, lookup': Lookup, key: Key)
  requires Inv(k, s)
  requires Flush(k, s, s', parentref, parent, childref, child, newchildref)
  requires IsPathFromRootLookup(k, BC.ViewOf(k.bck, s'.bcv), key, lookup')
  requires lookup == flushTransformLookupRev(lookup', parentref, parent, childref, child, newchildref);
  ensures IsPathFromRootLookup(k, BC.ViewOf(k.bck, s.bcv), key, lookup);
  ensures LookupIsAcyclic(lookup);
  ensures key in Last(lookup).node.children ==> Last(lookup).node.children[key] in BC.ViewOf(k.bck, s.bcv);
  decreases lookup'
  {
    if (|lookup'| == 0) {
    } else if (|lookup'| == 1) {
      assert BC.Root(k.bck) in BC.ViewOf(k.bck, s.bcv);
      assert lookup[0].node == BC.ViewOf(k.bck, s.bcv)[BC.Root(k.bck)];
      assert IsPathFromRootLookup(k, BC.ViewOf(k.bck, s.bcv), key, lookup);
    } else {
      FlushPreservesIsPathFromLookupRev(k, s, s', parentref, parent, childref, child, newchildref,
        flushTransformLookupRev(lookup'[.. |lookup'| - 1], parentref, parent, childref, child, newchildref),
        lookup'[.. |lookup'| - 1], key);

      assert IsPathFromRootLookup(k, BC.ViewOf(k.bck, s.bcv), key, lookup);
    }
  }

  lemma FlushPreservesAcyclicLookup(k: Constants, s: Variables, s': Variables, parentref: BC.Reference, parent: Node, childref: BC.Reference, child: Node, newchildref: BC.Reference, lookup': Lookup, key: Key)
  requires Inv(k, s)
  requires Flush(k, s, s', parentref, parent, childref, child, newchildref)
  requires IsPathFromRootLookup(k, BC.ViewOf(k.bck, s'.bcv), key, lookup')
  ensures LookupIsAcyclic(lookup')
  {
    var movedKeys := iset k | k in parent.children && parent.children[k] == childref;
    var newbuffer := imap k :: (if k in movedKeys then parent.buffer[k] + child.buffer[k] else child.buffer[k]);
    var newparentbuffer := imap k :: (if k in movedKeys then [] else parent.buffer[k]);
    var newparentchildren := imap k | k in parent.children :: (if k in movedKeys then newchildref else parent.children[k]);
    var newparent := Node(newparentchildren, newparentbuffer);

    if (|lookup'| <= 1) {
    } else {
      var lookup := flushTransformLookupRev(lookup', parentref, parent, childref, child, newchildref);
      FlushPreservesIsPathFromLookupRev(k, s, s', parentref, parent, childref, child, newchildref, lookup, lookup', key);
    }
  }

  lemma FlushPreservesAcyclic(k: Constants, s: Variables, s': Variables, parentref: BC.Reference, parent: Node, childref: BC.Reference, child: Node, newchildref: BC.Reference)
    requires Inv(k, s)
    requires Flush(k, s, s', parentref, parent, childref, child, newchildref)
    ensures Acyclic(k, s')
  {
    forall key, lookup':Lookup | IsPathFromRootLookup(k, BC.ViewOf(k.bck, s'.bcv), key, lookup')
    ensures LookupIsAcyclic(lookup')
    {
      FlushPreservesAcyclicLookup(k, s, s', parentref, parent, childref, child, newchildref, lookup', key);
    }
  }

  // Preservation proofs
  
  lemma GrowEquivalentLookups(k: Constants, s: Variables, s': Variables, oldroot: Node, newchildref: BC.Reference)
  requires Inv(k, s)
  requires Grow(k, s, s', oldroot, newchildref)
  ensures EquivalentLookups(k, s, s')
  {
    forall lookup:Lookup, key, value | IsSatisfyingLookup(k, BC.ViewOf(k.bck, s.bcv), key, value, lookup)
    ensures exists lookup' :: IsSatisfyingLookup(k, BC.ViewOf(k.bck, s'.bcv), key, value, lookup')
    {
      // Add one for the new root
      var rootref := BC.Root(k.bck);

      var newroot := BC.ViewOf(k.bck, s'.bcv)[rootref];

      //assert LookupIsAcyclic(lookup);

      var lookup' := [
        Layer(rootref, newroot, []),
        Layer(newchildref, oldroot, lookup[0].accumulatedBuffer)
      ] + lookup[1..];

      assert IsSatisfyingLookup(k, BC.ViewOf(k.bck, s'.bcv), key, value, lookup');
    }

    GrowPreservesAcyclic(k, s, s', oldroot, newchildref);
    
    forall lookup': Lookup, key, value | IsSatisfyingLookup(k, BC.ViewOf(k.bck, s'.bcv), key, value, lookup')
    ensures exists lookup :: IsSatisfyingLookup(k, BC.ViewOf(k.bck, s.bcv), key, value, lookup)
    {
      // Remove one for the root
      var lookup := lookup'[1..][0 := Layer(BC.Root(k.bck), lookup'[1].node, lookup'[1].accumulatedBuffer)];
      assert IsSatisfyingLookup(k, BC.ViewOf(k.bck, s.bcv), key, value, lookup);
    }
  }

  // Invariant proofs

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
    assert forall key :: MS.InDomain(key) ==> IsSatisfyingLookup(k, BC.ViewOf(k.bck, s.bcv), key, MS.EmptyValue(), [Layer(BC.Root(k.bck), EmptyNode(), [Insertion(MS.EmptyValue())])]);
  }

  lemma QueryStepPreservesInvariant<Value>(k: Constants, s: Variables, s': Variables, key: Key, value: Value, lookup: Lookup)
    requires Inv(k, s)
    requires Query(k, s, s', key, value, lookup)
    ensures Inv(k, s')
  {
  }
  
  lemma InsertMessageStepPreservesInvariant<Value>(k: Constants, s: Variables, s': Variables, key: Key, msg: BufferEntry, oldroot: Node)
    requires Inv(k, s)
    requires InsertMessage(k, s, s', key, msg, oldroot)
    ensures Inv(k, s')
  // {
  //   forall key1 | MS.InDomain(key1)
  //     ensures KeyHasSatisfyingLookup(k, s', key1)
  //   {
  //     var lookup: Lookup, value: Value :| IsSatisfyingLookup(k, BC.ViewOf(k.bck, s.bcv), key1, value, lookup);
  //     if key1 == key {
  //       assume false;
  //     } else {
  //       var newroot := AddMessageToNode(oldroot, key, msg);
  //       var newlookup := [Layer(BC.Root(k.bck), newroot, newroot.buffer[key1])] + lookup[1..];
  //       assert IsSatisfyingLookup(k, BC.ViewOf(k.bck, s'.bcv), key, value, newlookup);
  //     }
  //   }
  // }

  lemma FlushStepPreservesInvariant<Value>(k: Constants, s: Variables, s': Variables,
                                           parentref: BC.Reference, parent: Node, childref: BC.Reference, child: Node, newchildref: BC.Reference)
    requires Inv(k, s)
    requires Flush(k, s, s', parentref, parent, childref, child, newchildref)
    ensures Inv(k, s')
  // {
  // }
  
  lemma GrowStepPreservesInvariant<Value>(k: Constants, s: Variables, s': Variables, oldroot: Node, newchildref: BC.Reference)
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
