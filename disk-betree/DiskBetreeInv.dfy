include "MapSpec.dfy"
include "DiskBetree.dfy"
  
abstract module DiskBetreeInv {
  import opened DB : DiskBetree

  predicate KeyHasSatisfyingLookup<Value(!new)>(k: Constants, s: Variables, key: Key)
  {
    exists lookup, value :: IsSatisfyingLookup(k, s, key, value, lookup)
  }
  
  predicate Inv(k: Constants, s: Variables)
  {
    forall key | MS.InDomain(key) :: KeyHasSatisfyingLookup(k, s, key)
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
    assert forall key :: MS.InDomain(key) ==> IsSatisfyingLookup(k, s, key, MS.EmptyValue(), [Layer(BC.Root(k.bcc), EmptyNode(), [Insertion(MS.EmptyValue())])]);
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
  //     var lookup: Lookup, value: Value :| IsSatisfyingLookup(k, s, key1, value, lookup);
  //     if key1 == key {
  //       assume false;
  //     } else {
  //       var newroot := AddMessageToNode(oldroot, key, msg);
  //       var newlookup := [Layer(BC.Root(k.bcc), newroot, newroot.buffer[key1])] + lookup[1..];
  //       assert IsSatisfyingLookup(k, s', key, value, newlookup);
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
  // {
  // }

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
