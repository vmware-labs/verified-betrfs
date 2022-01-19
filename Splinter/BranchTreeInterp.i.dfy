include "../lib/Base/total_order.i.dfy"
include "IndirectionTable.i.dfy"
include "AllocationTable.i.dfy"
include "AllocationTableMachine.i.dfy"
include "MsgHistory.i.dfy"
include "BranchTree.i.dfy"
include "../Spec/Message.s.dfy"
include "../Spec/StampedMap.s.dfy"
include "../lib/Base/mathematics.i.dfy"

module BranchTreeInterpMod {
  import opened Options
  import opened ValueMessage
  import opened KeyType
  import opened StampedMapMod
  import opened DiskTypesMod
  import opened AllocationMod
  import opened MsgHistoryMod
  import IndirectionTableMod
  import opened BranchTreeMod
  import Nat_Order
  import opened Mathematics

  type Lookup = BranchPath

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

  lemma BranchLookupsEquivalentInductive(cache0: CacheIfc.Variables,
                                cache1: CacheIfc.Variables,
                                lookup0: BranchPath,
                                lookup1: BranchPath,
                                count : nat)
    requires lookup0.Valid(cache0)
    requires lookup1.Valid(cache1)
    requires lookup0.key == lookup1.key
    requires lookup0.Root() == lookup1.Root()
    requires 0 < count
    requires count <= |lookup0.steps|
    requires count <= |lookup1.steps|

    requires DiskViewsEquivalent(cache0.dv, cache1.dv, IReadsLookup(cache0, lookup0))
    requires DiskViewsEquivalent(cache1.dv, cache1.dv, IReadsLookup(cache1, lookup1))
    ensures forall i :: ((0 <= i < count) ==>  lookup0.steps[i] == lookup1.steps[i])
    {
      var key := lookup0.key;
      if 0 < count {
        // route to next node
        var nextStep0 := lookup0.steps[count-1];
        var nextStep1 := lookup1.steps[count-1];
        if 1 < count {
          BranchLookupsEquivalentInductive(cache0, cache1, lookup0, lookup1, count - 1);
          var step0 :=  lookup0.steps[count-2];
          var step1 :=  lookup1.steps[count-2];

          // This is equal from the induction
          assert step0.cu == step1.cu; // All we need to show is that the CUs are the same
          assert CUToBranchNode(step0.cu, cache0) == CUToBranchNode(step1.cu, cache1);

          assert lookup0.LinkedAt(count-1) by {
            lookup0.reveal_Linked();
          }

          assert lookup1.LinkedAt(count-1) by {
            lookup1.reveal_Linked();
          }

          assert step0.node.nextStep(key) == nextStep0.cu;
          assert step1.node.nextStep(key) == nextStep1.cu;

          assert nextStep0.cu == nextStep1.cu;
      }
        // we need to show that nextStep cu is in IReads
        reveal_IReadsLookup();
        assert nextStep0.cu in CUsInDisk();  // try to trigger set comprehension
        assert nextStep0.cu in lookup0.CUs();
        assert nextStep0.cu in IReadsLookup(cache0, lookup0);
        assert nextStep1.cu in IReadsLookup(cache1, lookup1);

        assert nextStep0.cu == nextStep1.cu;
        assert nextStep0.node.Valid(cache0);
        assert CUToBranchNode(nextStep0.cu, cache0) == CUToBranchNode(nextStep1.cu, cache1);
        assert nextStep0.node == nextStep1.node;

        // route to next node
        assert nextStep0 == nextStep1;
      }
  }

    lemma BranchLookupsEquivalent(cache0: CacheIfc.Variables,
                                  cache1: CacheIfc.Variables,
                                  receipt0: BranchReceipt,
                                  receipt1: BranchReceipt)

        //requires ValidLookupForBranchEquivalent(cache0, cache1, receipt0, receipt1)
        requires DiskViewsEquivalent(cache0.dv, cache1.dv, IReadsLookup(cache0, receipt0.branchPath))
        requires receipt0.Key() == receipt1.Key()
        requires receipt0.Valid(cache0)
        requires receipt1.Valid(cache1)
        requires receipt0.branchTree == receipt1.branchTree
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
     && (forall i | 0 <= i < |receipts0| :: receipts0[i].branchTree == receipts1[i].branchTree)
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
        assert receipts0[count-1].Root() == receipts1[count-1].Root();
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

module BranchTreeInterpIfc {
  export
    provides
      BranchTreeInterpMod,
      BranchTop,
      BranchReceipt,
      BranchReceipt.WF,
      BranchReceipt.Key,
      BranchReceipt.Decode,
      BranchReceipt.Valid,
      BranchReceipt.ValidCUs,
      BranchReceipt.CUs,
      BranchReceipt.Top,
      BranchReceipt.IReads,
      Skolem,
      BranchLookupEquivalentRequirements,
      BranchReceiptsEquivalent
    reveals
      BranchLookupEquivalentRequirements

  import BranchTreeInterpMod

  datatype BranchTop = BranchTop(base: BranchTreeInterpMod.BranchTreeMod.Variables)
  datatype BranchReceipt = BranchReceipt(base: BranchTreeInterpMod.BranchTreeMod.BranchReceipt)
  {
    predicate WF() { base.WF() }
    function Key() : BranchTreeInterpMod.BranchTreeMod.KeyType.Key { base.Key() }
    function Decode() : BranchTreeInterpMod.BranchTreeMod.Options.Option<BranchTreeInterpMod.BranchTreeMod.ValueMessage.Message> { base.branchPath.Decode() }
    //predicate ValidCUs(cus:seq<BranchTreeInterpMod.BranchTreeMod.DiskTypesMod.CU>) { base.ValidCUs(cus) }
    predicate Valid(cache: BranchTreeInterpMod.BranchTreeMod.CacheIfc.Variables) { base.Valid(cache) }
    predicate ValidCUs() { base.ValidCUs() }
    function CUs() : seq<BranchTreeInterpMod.BranchTreeMod.DiskTypesMod.CU> { base.branchPath.CUs() }
    function Top() : BranchTop { BranchTop(base.branchTree) }
    function IReads(cache: BranchTreeInterpMod.BranchTreeMod.CacheIfc.Variables) : set<BranchTreeInterpMod.BranchTreeMod.DiskTypesMod.CU> { BranchTreeInterpMod.IReadsLookup(cache, base.branchPath) }
  }
  datatype Skolem = Skolem(base: BranchTreeInterpMod.BranchTreeMod.Skolem)

   // Need to expose this body so caller can satisfy it.
   predicate BranchLookupEquivalentRequirements(
    key: BranchTreeInterpMod.BranchTreeMod.KeyType.Key,
    cache0: BranchTreeInterpMod.BranchTreeMod.CacheIfc.Variables,
    cache1: BranchTreeInterpMod.BranchTreeMod.CacheIfc.Variables,
    receipts0: seq<BranchReceipt>,
    receipts1: seq<BranchReceipt>)
   {
     && |receipts0| == |receipts1|
     && (forall i | 0 <= i < |receipts0| :: receipts0[i].Valid(cache0))
     && (forall i | 0 <= i < |receipts0| :: receipts0[i].Key() == key)
     && (forall i | 0 <= i < |receipts1| :: receipts1[i].Valid(cache1))
     && (forall i | 0 <= i < |receipts1| :: receipts1[i].Key() == key)
     && (forall i | 0 <= i < |receipts0| :: receipts0[i].Top() == receipts1[i].Top())
     && (forall i | 0 <= i < |receipts0| :: BranchTreeInterpMod.AllocationMod.DiskViewsEquivalent(cache0.dv, cache1.dv, receipts0[i].IReads(cache0)))
   }
//  predicate BranchLookupEquivalentRequirements(
//    key: BranchTreeInterpMod.BranchTreeMod.KeyType.Key,
//    cache0: BranchTreeInterpMod.BranchTreeMod.CacheIfc.Variables,
//    cache1: BranchTreeInterpMod.BranchTreeMod.CacheIfc.Variables,
//    receipts0: seq<BranchReceipt>,
//    receipts1: seq<BranchReceipt>)
//  {
//    var rr0 := seq(|receipts0|, i=>receipts0[i].base);
//    var rr1 := seq(|receipts1|, i=>receipts1[i].base);
//    BranchTreeInterpMod.BranchLookupEquivalentRequirements(key, cache0, cache1, rr0, rr1)
//  }

  lemma BranchReceiptsEquivalent(
    key: BranchTreeInterpMod.BranchTreeMod.KeyType.Key,
    cache0: BranchTreeInterpMod.BranchTreeMod.CacheIfc.Variables,
    cache1: BranchTreeInterpMod.BranchTreeMod.CacheIfc.Variables,
    receipts0: seq<BranchReceipt>,
    receipts1: seq<BranchReceipt>)
    requires BranchLookupEquivalentRequirements(key, cache0, cache1, receipts0, receipts1)
    ensures receipts0 == receipts1
  {
    var baseReceipts0 := seq(|receipts0|, i requires 0<=i<|receipts0| => receipts0[i].base);
    var baseReceipts1 := seq(|receipts0|, i requires 0<=i<|receipts0| => receipts1[i].base);
    BranchTreeInterpMod.BranchReceiptsEquivalent(key, cache0, cache1, baseReceipts0, baseReceipts1);
  }
}
