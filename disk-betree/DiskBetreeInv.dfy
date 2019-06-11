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

  //// Definitions for lookup preservation

  // One-way preservation

  predicate PreservesLookups<Value(!new)>(k: Constants, s: Variables, s': Variables)
  {
    forall lookup, key, value :: IsSatisfyingLookup(k, s, key, value, lookup) ==>
      exists lookup' :: IsSatisfyingLookup(k, s', key, value, lookup')
  }

  predicate PreservesLookupsExcept<Value(!new)>(k: Constants, s: Variables, s': Variables, exceptQuery: Key)
  {
    forall lookup, key, value :: key != exceptQuery && IsSatisfyingLookup(k, s, key, value, lookup) ==>
      exists lookup' :: IsSatisfyingLookup(k, s', key, value, lookup')
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
    && exists lookup :: IsSatisfyingLookup(k, s', key, value, lookup)
  }

  // Preservation proofs

  lemma GrowEquivalentLookups(k: Constants, s: Variables, s': Variables, oldroot: Node, newchildref: BC.Reference)
  requires Grow(k, s, s', oldroot, newchildref)
  ensures EquivalentLookups(k, s, s')
  {
    forall lookup:Lookup, key, value | IsSatisfyingLookup(k, s, key, value, lookup)
    ensures exists lookup' :: IsSatisfyingLookup(k, s', key, value, lookup')
    {
      // Add one for the new root
      var rootref := BC.Root(k.bcc);

      // TODO need to have contract that read matches the write
      var newroot := BC.Read(k.bcc, s'.bcv, rootref);
      assert newroot == Node(imap key | MS.InDomain(key) :: newchildref, imap key | MS.InDomain(key) :: []);

      var lookup' := [
        Layer(rootref, newroot, []),
        Layer(newchildref, oldroot, lookup[0].accumulatedBuffer)
      ] + lookup[1..];

      forall i | 0 <= i < |lookup'|
      ensures BC.Read(k.bcc, s'.bcv, lookup'[i].ref) == lookup'[i].node
      ensures WFNode(lookup'[i].node)
      {
        if (i == 0) {
          assert BC.Read(k.bcc, s'.bcv, lookup'[i].ref) == lookup'[i].node;

          forall k ensures k in newroot.buffer
          {
            assert MS.InDomain(k);
          }
          assert WFNode(lookup'[i].node);
        } else if (i == 1) {
          // TODO need a contract from alloc here:
          assert BC.Read(k.bcc, s'.bcv, lookup'[i].ref) == lookup'[i].node;

          assert WFNode(lookup'[i].node);
        } else {
          // TODO need to have contract that allows this to be preserved:
          assert BC.Read(k.bcc, s.bcv, lookup'[i].ref) == lookup'[i].node;
          assert BC.Read(k.bcc, s'.bcv, lookup'[i].ref) == lookup'[i].node;

          assert WFNode(lookup'[i].node);
        }
      }

      forall i | 0 <= i < |lookup'| - 1
      ensures key in lookup'[i].node.children
      ensures lookup'[i].node.children[key] == lookup'[i+1].ref
      {
        if (i == 0) {
          assert key in lookup'[i].node.children;
          assert lookup'[i].node.children[key] == lookup'[i+1].ref;
        } else if (i == 1) {
          assert key in lookup'[i].node.children;
          assert lookup'[i].node.children[key] == lookup'[i+1].ref;
        } else {
          assert key in lookup'[i].node.children;
          assert lookup'[i].node.children[key] == lookup'[i+1].ref;
        }
      }

      assert IsSatisfyingLookup(k, s', key, value, lookup');
    }

    forall lookup, key, value | IsSatisfyingLookup(k, s', key, value, lookup)
    ensures exists lookup' :: IsSatisfyingLookup(k, s, key, value, lookup')
    {
      // Remove one for the root
      var lookup' := lookup[1..];
      assert IsSatisfyingLookup(k, s, key, value, lookup');
    }
  }

  // Invariant proofs

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
