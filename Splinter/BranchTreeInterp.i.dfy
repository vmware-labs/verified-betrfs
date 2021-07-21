include "../lib/Base/total_order.i.dfy"
include "IndirectionTable.i.dfy"
include "AllocationTable.i.dfy"
include "AllocationTableMachine.i.dfy"
include "MsgHistory.i.dfy"
include "BranchTree.i.dfy"
include "../Spec/Message.s.dfy"
include "../Spec/Interp.s.dfy"
include "../lib/Base/mathematics.i.dfy"

module BranchTreeInterpMod {
  import opened Options
  import opened ValueMessage
  import opened KeyType
  import opened InterpMod
  import opened DiskTypesMod
  import opened AllocationMod
  import opened MsgHistoryMod
  import IndirectionTableMod
  import opened BranchTreeMod
  import Nat_Order
  import opened Mathematics

  type Lookup = BranchPath


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

  predicate ValidLookupHasCU(cache: CacheIfc.Variables, lookup: BranchPath, cu: CU)
  {
    && lookup.Valid(cache)
    && cu in lookup.CUs()
  }

  // IREAds lookup
  function {:opaque} IReadsLookup(cache: CacheIfc.Variables, lookup: BranchPath) : set<CU> {
    set cu:CU |
       && cu in CUsInDisk()
       && ValidLookupHasCU(cache, lookup, cu)
      :: cu
  }

  predicate StepsEquivalent(cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, step0: BranchStep, step1: BranchStep)
  {
    //&& step0.cu == step1.cu
    && step0.Valid(cache0)
    && step1.Valid(cache1)
    && step0.cu == step1.cu
    && CUToBranchNode(step0.cu, cache0) == CUToBranchNode(step1.cu, cache1)
  }

  predicate StepsLinked(cache: CacheIfc.Variables, lookup: BranchPath, currStep: nat, currStepCU: CU, nextStepCU : CU)
    requires currStep < |lookup.steps| - 1
  {
    // make sure cus match with the ones in the branchpath
    && currStepCU == lookup.steps[currStep].cu
    && nextStepCU == lookup.steps[currStep+1].cu
    // The lookup has to be valid
    && lookup.Valid(cache)
    // make sure there's a valid link at the lookup -- Might not be needed, we might be getting this from Valid(s)
    && lookup.LinkedAt(currStep+1)
    // Check if these loose steps correspond to parent-child
    && var currNode := CUToBranchNode(currStepCU, cache);
    && var nextNode := CUToBranchNode(nextStepCU, cache);
    && currNode.Some?
    && nextNode.Some?
    && currNode.value == lookup.steps[currStep].node
    && nextNode.value == lookup.steps[currStep+1].node
  }

  lemma BranchLookupsEquivalentInductive(
                                cache0: CacheIfc.Variables,
                                cache1: CacheIfc.Variables,
                                lookup0: BranchPath,
                                lookup1: BranchPath,
                                count : nat)
    requires lookup0.key == lookup1.key
    requires lookup0.Valid(cache0)
    requires lookup1.Valid(cache1)
    requires 0 < count
    requires count <= |lookup0.steps|
    requires count <= |lookup1.steps|
    //requires lookup0.steps[0].cu == lookup1.steps[0].cu
    requires DiskViewsEquivalent(cache0.dv, cache1.dv, IReadsLookup(cache0, lookup0))
    requires DiskViewsEquivalent(cache1.dv, cache1.dv, IReadsLookup(cache1, lookup1))
    ensures forall i :: ((0 < i < count-1) ==>  && StepsLinked(cache0, lookup0, i, lookup0.steps[i].cu, lookup0.steps[i+1].cu)
                                                && StepsLinked(cache1, lookup1, i, lookup1.steps[i].cu, lookup1.steps[i+1].cu))
    ensures forall i :: ((0 <= i < count) ==> StepsEquivalent(cache0, cache1, lookup0.steps[i], lookup1.steps[i]))
    {
      if 1 < count {
        BranchLookupsEquivalentInductive(cache0, cache1, lookup0, lookup1, count - 1);
        var step0 :=  lookup0.steps[count-2];
        var step1 :=  lookup1.steps[count-2];

        //assert step0.cu in IReadsLookup(cache0, lookup0);
        //assert step1.cu in IReadsLookup(cache0, lookup0);

        assert step0.cu == step1.cu; // All we need to show is that the CUs are the same
        assert CUToBranchNode(step0.cu, cache0) == CUToBranchNode(step1.cu, cache1);

        // route to next node
        var nextStep0 := lookup0.steps[count-1];
        var nextStep1 := lookup1.steps[count-1];

        assert StepsEquivalent(cache0, cache1, step0, step1);
        assert StepsEquivalent(cache0, cache1, nextStep0, nextStep1);
        assert StepsLinked(cache0, lookup0, count-1, step0.cu, nextStep0.cu);
        assert StepsLinked(cache1, lookup1, count-1, step1.cu, nextStep1.cu);

      } else {
        assert count == 1;
      }
    }

    lemma BranchLookupsEquivalent(cache0: CacheIfc.Variables,
                                  cache1: CacheIfc.Variables,
                                  receipt0: BranchReceipt,
                                  receipt1: BranchReceipt)

        //requires ValidLookupForBranchEquivalent(cache0, cache1, receipt0, receipt1)
        requires DiskViewsEquivalent(cache0.dv, cache1.dv, IReadsLookup(cache0, receipt0.branchPath))
        ensures  receipt0 == receipt1
     {
        var lookup0 := receipt0.branchPath;
        var lookup1 := receipt1.branchPath;
        var minLookup := min(|lookup0.steps|, |lookup1.steps|);
        BranchLookupsEquivalentInductive(cache0, cache1, lookup0, lookup1, minLookup);
      }

    /*
     * Lemmas about sequences of branch Receipts
     *
     *
     */
   predicate BranchLookupEquivalentRequirements(key: Key,
                                    cache0: CacheIfc.Variables,
                                    cache1: CacheIfc.Variables,
                                    receipts0: seq<BranchReceipt>,
                                    receipts1: seq<BranchReceipt>)
   {

     && |receipts0| == |receipts1|
     && (forall i | 0 <= i < |receipts0| :: receipts0[i].Valid(cache0))
     && (forall i | 0 <= i < |receipts0| :: receipts0[i].branchPath.key == key)
     && (forall i | 0 <= i < |receipts1| :: receipts1[i].Valid(cache1))
     && (forall i | 0 <= i < |receipts1| :: receipts1[i].branchPath.key == key)
     && (forall i | 0 <= i < |receipts0| :: receipts0[i].branchTree.Root() == receipts1[i].branchTree.Root() )
     && (forall i | 0 <= i < |receipts0| :: DiskViewsEquivalent(cache0.dv, cache1.dv, IReadsLookup(cache0, receipts0[i].branchPath)))
   }


   lemma BranchReceiptsEquivalentInductive(key: Key,
                                    cache0: CacheIfc.Variables,
                                    cache1: CacheIfc.Variables,
                                    receipts0: seq<BranchReceipt>,
                                    receipts1: seq<BranchReceipt>,
                                    count: nat)
      requires BranchLookupEquivalentRequirements(key, cache0, cache1, receipts0, receipts1)
      requires count <= |receipts0|
      ensures forall i | 0 <= i < count :: receipts0[i] == receipts1[i]
    {
      if (0 < count) {
        BranchReceiptsEquivalentInductive(key, cache0, cache1, receipts0, receipts1, count-1);
        //RootEquivalentForBranchReceipt(cache0, cache1, receipts0[count-1], receipts1[count-1]);
        BranchLookupsEquivalent(cache0, cache1, receipts0[count-1], receipts1[count-1]);
      }
    }

    lemma BranchReceiptsEquivalent(key: Key,
                                  cache0: CacheIfc.Variables,
                                  cache1: CacheIfc.Variables,
                                  receipts0: seq<BranchReceipt>,
                                  receipts1: seq<BranchReceipt>)


      requires BranchLookupEquivalentRequirements(key, cache0, cache1, receipts0, receipts1)
      //ensures forall i | 0 <= i < min(|receipts0|, |receipts1|) :: RootEquivalentForBranchReceipt(cache0, cache1, receipts0[i], receipts1[i])
      ensures forall i | 0 <= i < min(|receipts0|, |receipts1|) :: receipts0[i] == receipts1[i]
      ensures |receipts0| == |receipts1|
    {

      var count := min(|receipts0|, |receipts1|);
      BranchReceiptsEquivalentInductive(key, cache0, cache1, receipts0, receipts1, count);
    }

}
