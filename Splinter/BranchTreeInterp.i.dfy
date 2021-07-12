include "../lib/Base/total_order.i.dfy"
include "IndirectionTable.i.dfy"
include "AllocationTable.i.dfy"
include "AllocationTableMachine.i.dfy"
include "MsgHistory.i.dfy"
include "BranchTree.i.dfy"
include "SplinterTree.i.dfy"
include "../Spec/Message.s.dfy"
include "../Spec/Interp.s.dfy"
include "../lib/Base/mathematics.i.dfy"

module BranchTreeInterpMod {
  import opened Options
  import opened ValueMessage
  import KeyType
  import opened InterpMod
  import opened DiskTypesMod
  import opened AllocationMod
  import opened MsgHistoryMod
  import IndirectionTableMod
  import opened BranchTreeMod
  import SplinterTreeMachineMod
  import Nat_Order
  import opened Mathematics

  type Lookup = BranchPath

  //function IMLookup()

  // NOtE: These might not be needed.
  function IMKey(root: CU, cache: CacheIfc.Variables, key: Key) : Message
  {
    if exists msg, sk :: Query(root, cache, key, msg, sk) // always true by invariant
    then
      var msg, sk :| Query(root, cache, key, msg, sk);
      if msg.Some?
      then
        msg.value
      else
        DefaultMessage()
    else
      // We should never get here
      DefaultMessage()
  }

  function IM(root : CU, cache: CacheIfc.Variables) : imap<Key, Message>
  {
    imap k | true :: IMKey(root, cache, k)
  }

  function IReadsKey(v: Variables, cache: CacheIfc.Variables, key: Key) : set<CU>

  function IReads(v: Variables, cache: CacheIfc.Variables) : set<CU>

  lemma BranchLookupsEquivalentInductive(v: Variables,
                                cache0: CacheIfc.Variables,
                                cache1: CacheIfc.Variables,
                                lookup0: BranchPath,
                                lookup1: BranchPath,
                                count : nat)
    requires lookup0.key == lookup1.key
    requires lookup0.Valid(cache0)
    requires lookup1.Valid(cache1)
    requires count <= |lookup0.steps|
    requires count <= |lookup1.steps|
    requires DiskViewsEquivalent(cache0.dv, cache1.dv, IReads(v, cache0))
    ensures forall i :: ((0 <= i < count) ==> (lookup0.steps[i] == lookup1.steps[i]))
    {
      if count == 0 {

      } else {
        BranchLookupsEquivalentInductive(v, cache0, cache1, lookup0, lookup1, count - 1);
        var step0 :=  lookup0.steps[count-1];
        var step1 :=  lookup1.steps[count-1];
      }
    }


    lemma BranchLookupsEquivalent(v: Variables,
                                  cache0: CacheIfc.Variables,
                                  cache1: CacheIfc.Variables,
                                  lookup0: BranchPath,
                                  lookup1: BranchPath)
      requires lookup0.key == lookup1.key
      requires lookup0.Valid(cache0)
      requires lookup1.Valid(cache1)
      requires DiskViewsEquivalent(cache0.dv, cache1.dv, IReads(v, cache0))
      ensures  lookup0 == lookup1
      {
        var minLookup := min(|lookup0.steps|, |lookup1.steps|);
        BranchLookupsEquivalentInductive(v, cache0, cache1, lookup0, lookup1, minLookup);
      }

}
