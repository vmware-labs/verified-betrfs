// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/total_order.i.dfy"
include "IndirectionTable.i.dfy"
include "AllocationTable.i.dfy"
include "AllocationTableMachine.i.dfy"
include "CoordinationLayer/MsgHistory.i.dfy"
include "SplinterTree.i.dfy"
include "BranchTreeInterp.i.dfy"
include "../Spec/Message.s.dfy"
include "CoordinationLayer/StampedMap.i.dfy"
include "../lib/Base/mathematics.i.dfy"

// interpretation for the SplinterTree Implementation
// Go through this is and replace all placeholders
module SplinterTreeInterpMod {
  import opened Options
  import opened ValueMessage
  import opened KeyType
  import opened StampedMapMod
  import opened DiskTypesMod
  import opened AllocationMod
  import opened MsgHistoryMod
  import IndirectionTableMod
  import opened SplinterTreeMachineMod
  import Nat_Order
  import opened SequenceSetsMod
  import opened Mathematics


  // Select the messages that lookup finds.
  function LookupToMessage(lookup: TrunkPath, v : Variables, cache: CacheIfc.Variables) : (outm : Message)
    requires lookup.Valid(v, cache)
    ensures outm.Define?
  {
    lookup.Decode()
  }

  predicate {:opaque} LookupExists(v: Variables, cache: CacheIfc.Variables, key: Key)
  {
    exists lookup :: ValidLookup(v, cache, key, lookup)
  }

  function IMLookup(v: Variables, cache: CacheIfc.Variables, key: Key) : (lookup: TrunkPath)
    requires LookupExists(v, cache, key)
    ensures ValidLookup(v, cache, key, lookup)
    ensures lookup.WF()
  {
    reveal_LookupExists();
    var lookup :| ValidLookup(v, cache, key, lookup);
    lookup
  }

  // Produce a receipt for this key
  function IMKey(v: Variables, cache: CacheIfc.Variables, key: Key) : (m: Message)
    ensures m.Define?
  {
    if LookupExists(v, cache, key) // Always true by invariant
    then
      LookupToMessage(IMLookup(v, cache, key), v, cache)
    else
      DefaultMessage() // this is not a absence of a key, this case cannot happen by invariant
  }

  function {:opaque} IM(cache: CacheIfc.Variables, v: Variables) : (i:StampedMap)
    ensures i.seqEnd == v.endSeq
  {
    RawInterp((imap key | AnyKey(key) :: IMKey(v, cache, key)), v.endSeq) // check v.endSeq used to be sb.endSeq
  }

  predicate DiskSupportsVariables(v: Variables, dv: DiskView, sb: Superblock)
  {
    && IndirectionTableMod.DurableAt(v.indTbl, CacheIfc.Variables(dv), sb.indTbl)
    && v.memBuffer.Keys == {}
    && v.endSeq == sb.endSeq
    && v.frozen.Idle?
    && v.root == sb.root
  }

  function EmptyVars(sb: Superblock) : Variables
  {
    Variables(
      0,       // endSeq
      sb.root, // tree root (must be given to us)
      IndirectionTableMod.Empty(),
      map[],   // empty memBuffer
      Idle     // frozen
    )
  }
  
  function SynthesizeRunningVariables(dv: DiskView, sb: Superblock) : Variables
  {
    if exists v :: DiskSupportsVariables(v, dv, sb)
    then var v :| DiskSupportsVariables(v, dv, sb); v
    else EmptyVars(sb)
  }

  predicate AllLookupsExist(v: Variables, cache: CacheIfc.Variables)
  {
    forall key | AnyKey(key) :: LookupExists(v, cache, key)
  }

  predicate LookupRootsequivalent(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, lookup0 : TrunkPath, lookup1: TrunkPath)
  {
    && lookup0.Valid(v, cache0)
    && lookup1.Valid(v, cache1)
    && var root0 := lookup0.steps[0].na;
    && var root1 := lookup1.steps[0].na;
    && root0.cu == root1.cu
  }

  lemma RecieptCUsSubsetOfIReads(v: Variables, cache: CacheIfc.Variables, lookup: TrunkPath, step: TrunkStep, idx: nat)
    requires lookup.Valid(v, cache)
    requires step in lookup.steps
    requires 0 <= idx < |step.branchReceipts|
    ensures step.branchReceipts[idx].IReads(cache) <= IReads(v, cache)
  {
    assert forall cu | cu in step.CUs() :: cu in lookup.CUs();
    forall cu | cu in step.branchReceipts[idx].IReads(cache)
       ensures cu in IReads(v, cache) {
         //BranchTreeInterpMod.reveal_IReadsLookup();
         reveal_IReads();
         assert cu in CUsInDisk();

         assert ValidLookupHasCU(v, cache, lookup, cu); // Witness

    }
    //BranchTreeInterpMod.reveal_IReadsLookup();
    reveal_IReads();
  }

  lemma LookupsEquivalent(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, lookup0 : TrunkPath, lookup1: TrunkPath, count : nat)
    requires lookup0.k == lookup1.k
    requires lookup0.Valid(v, cache0)
    requires lookup1.Valid(v, cache1)
    requires count <= |lookup0.steps|
    requires count <= |lookup1.steps|
    requires LookupRootsequivalent(v, cache0, cache1, lookup0, lookup1)
    requires DiskViewsEquivalent(cache0.dv, cache1.dv, IReads(v, cache0))
    ensures forall i :: ((0 <= i < count) ==> (lookup0.steps[i] == lookup1.steps[i]))
  {
      if 0 < count
      {
        var nextstep0 := lookup0.steps[count-1];
        var nextstep1 := lookup1.steps[count-1];
        if (count == 1) {
          // they share roots
          assert nextstep0.na.cu == nextstep1.na.cu;
          // assert nextstep0.na == nextstep1.na;
        } else {
          LookupsEquivalent(v, cache0, cache1, lookup0, lookup1, count-1);
          var step0 := lookup0.steps[count-2];
          var step1 := lookup1.steps[count-2];

          var key := lookup0.k;

          assert step0 == step1; // the previous steps are the same by induction

          // Linking establishes the relationship between nextstep and step
          assert lookup0.LinkedAt(count-1);
          assert lookup1.LinkedAt(count-1);

          // Probably not needed now but check.
          // we know step0==step1 and the we try to establish that step0 Links nextStep0 and step1 Links nextStep1
          assert step0.na.node.nextStep(key) == nextstep0.na.cu;
          assert step1.na.node.nextStep(key) == nextstep1.na.cu;
        }

        assert nextstep0.na.cu == nextstep1.na.cu;

        // nextstep0.cu is in IReads
        assert nextstep0.na.cu in CUsInDisk();  // try to trigger set comprehension
        assert nextstep1.na.cu in lookup0.CUs();
        assert ValidLookupHasCU(v, cache0, lookup0, nextstep0.na.cu);
        assert nextstep0.na.cu in IReads(v, cache0) by {
          reveal_IReads();
        }

        // nextstep1.cu is in IReads
        assert nextstep1.na.cu in CUsInDisk();  // try to trigger set comprehension
        assert nextstep1.na.cu in lookup1.CUs();
        assert ValidLookupHasCU(v, cache1, lookup1, nextstep1.na.cu);
        assert nextstep1.na.cu in IReads(v, cache1) by {
          reveal_IReads();
        }

         // Since they're in the IReadsSet, the nodes are also the same
          assert nextstep0.na.node == nextstep1.na.node;

//          assert nextstep0.na.node.InIndTable(v);
//          assert nextstep1.na.node.InIndTable(v);
          assert v.indTbl[nextstep0.na.id] == nextstep0.na.cu;
          assert v.indTbl[nextstep1.na.id] == nextstep1.na.cu;
          assert nextstep0.na.id == nextstep1.na.id;

          assert nextstep0.na == nextstep1.na;
          forall i | 0 <= i < |nextstep0.branchReceipts| ensures
                  DiskViewsEquivalent(cache0.dv, cache1.dv, nextstep0.branchReceipts[i].IReads(cache0))
          {

             RecieptCUsSubsetOfIReads(v, cache0, lookup0, nextstep0, i);
             assert nextstep0.branchReceipts[i].IReads(cache0) <= IReads(v, cache0);
          }

          BranchTreeInterpIfc.BranchReceiptsEquivalent(lookup0.k, cache0, cache1, nextstep0.branchReceipts, nextstep1.branchReceipts);
          assert nextstep0.branchReceipts == nextstep1.branchReceipts; // need to make it believe this
          assert nextstep0 == nextstep1;

      }
  }

  lemma IMExtensionality(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables)
    requires forall key | AnyKey(key) :: IMKey(v, cache0, key) == IMKey(v, cache1, key)
    ensures IM(cache0, v) == IM(cache1, v)
  {
    reveal_IM();
  }

//  predicate Invariant(v: Variables, cache: CacheIfc.Variables)
//  {
//    && v.WF()
//    && cache.WF()
////    && v.AllLookupsExist(v, cache)
//  }

  // TODO; Might need to change this to table about both IM and IMStable
  lemma Framing(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables)
    requires DiskViewsEquivalent(cache0.dv, cache1.dv, IReads(v, cache0))
//    requires AllLookupsExist(v, cache0)
//    requires AllLookupsExist(v, cache1)
    ensures IM(cache0, v) == IM(cache1, v)
  {
    // TODO I'm surprised this proof passes easily.
    // narrator: It doesn't.
    // Sowmya : Plot twist .. Now it times out :)
    // It doesn't after I changed lookups to account for the memBuffer
    // TODO: Check the Implementation of lookup
    forall key | AnyKey(key) //
      ensures IMKey(v, cache0, key) == IMKey(v, cache1, key)
    {
      assert LookupExists(v, cache0, key);
      assert LookupExists(v, cache1, key);

      //assert IReads(v, cache0) == IReads(v, cache1);
      var lookup0 := IMLookup(v, cache0, key);
      var lookup1 := IMLookup(v, cache1, key);

      var count := min(|lookup0.steps|, |lookup1.steps|);
      LookupsEquivalent(v, cache0, cache1, lookup0, lookup1, count);
      assert lookup0 == lookup1;
    }
    // TODO there's still a timeout lurking here. Jon kicked it down
    // the road by factoring out IMExtensionality, but the underlying
    // cause is still here and we haven't found it.
    IMExtensionality(v, cache0, cache1);
  }

  lemma PutEffect(v: Variables, v': Variables, cache: CacheIfc.Variables, cache': CacheIfc.Variables, key: Key, value: Value, sk: Skolem)
    ensures IM(cache', v') == IM(cache, v).Put(key, Define(value))
  {
    assume false; // This is hard to prove -- we need to finish a tree
  }

  /*
   * NonEquivocate: Ensure if IMLookup returns a valid lookup, that its the only valid lookup that can ever be
   * returned by IMLookup
   */
  lemma NonEquivocateForLookup(v: Variables, cache : CacheIfc.Variables, key: Key, lookup: TrunkPath)
    requires ValidLookup(v, cache, key, lookup)
    ensures IMLookup(v, cache, key) == lookup
  {

  }

  // Show that Flushes across trunk nodes preserve the invariant
  lemma FlushEffect(v: Variables, v': Variables, cache: CacheIfc.Variables, cache': CacheIfc.Variables, cacheOps: CacheIfc.Ops, sk: Skolem)
    requires sk.FlushStep?
    requires AllLookupsExist(v, cache)
    requires AllLookupsExist(v, cache')
    requires Flush(v, v', cache, cacheOps, sk)
    ensures IM(cache', v') == IM(cache, v)
  {
    forall key | AnyKey(key)
      ensures IMKey(v', cache', key) == IMKey(v, cache, key)
    {
      var rec := sk.flush;
      assert LookupExists(v, cache, key);
      assert LookupExists(v, cache', key);

      //assert IReads(v, cache0) == IReads(v, cache1);
      //var lookup := IMLookup(v, cache, key);
      var lookup' := IMLookup(v, cache', key);
      var lookup;

      // If  newParent and newChild are in lookup'
      if (rec.newParent.cu in lookup'.CUs() && rec.newChild.cu in lookup'.CUs())
      {
        assume false;
      } else if (rec.newParent.cu in lookup'.CUs()) {
          // If  [newParent is in lookup'] -- idx | lookup'.steps[idx] == newParent
          assume false;
      } else {
          // else lookup == lookup'
          assume false;
          lookup := lookup';
      }
      // TODO
      assert IMKey(v', cache', key) == IMKey(v, cache, key);
    }
    assume false;
    assert IM(cache', v') == IM(cache, v);
  }

  // Show that compactions preserve the invariant
  lemma CompactionEffect(v: Variables, v': Variables, cache: CacheIfc.Variables, cache': CacheIfc.Variables, cacheOps: CacheIfc.Ops, sk: Skolem)
    requires sk.CompactBranchStep?
    requires CompactBranch(v, v', cache, cacheOps, sk)
    ensures IM(cache', v') == IM(cache, v)
  {
    assume false;
  }

  // Show that draining the memBuffer preserves the invariant
  lemma DrainMemBufferEffect(v: Variables, v': Variables, cache: CacheIfc.Variables, cache': CacheIfc.Variables, cacheOps: CacheIfc.Ops, sk: Skolem)
    requires sk.DrainMemBufferStep?
    requires DrainMemBuffer(v, v', cache, cacheOps, sk)
    ensures IM(cache', v') == IM(cache, v)
  {
    assume false;
  }

  // All the SplinterTree Internal steps shouldn't affect the interpretation
  lemma InternalStepLemma(v: Variables, v': Variables, cache: CacheIfc.Variables, cache': CacheIfc.Variables, cacheOps: CacheIfc.Ops, sk: Skolem)
    requires sk.FlushStep? || sk.DrainMemBufferStep? || sk.CompactBranchStep?
    requires Internal(v, v', cache, cacheOps, sk)
    ensures IM(cache', v') == IM(cache, v)
  {
    match sk {
     case FlushStep(flush: FlushRec) => {
        FlushEffect(v, v', cache, cache', cacheOps, sk);
     }
     case DrainMemBufferStep(oldRoot: NodeAssignment, newRoot: NodeAssignment) => {
        DrainMemBufferEffect(v, v', cache, cache', cacheOps, sk);
     }
     case CompactBranchStep(receipt: CompactReceipt) => {
        CompactionEffect(v, v', cache, cache', cacheOps, sk);
     }
    }
  }

}
