// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/total_order.i.dfy"
include "IndirectionTable.i.dfy"
include "AllocationTable.i.dfy"
include "AllocationTableMachine.i.dfy"
include "MsgHistory.i.dfy"
include "SplinterTree.i.dfy"
include "../Spec/Message.s.dfy"
include "../Spec/Interp.s.dfy"

// interpretation for the SplinterTree Implementation
// Go through this is and replace all placeholders
module SplinterTreeInterpMod {
  import opened Options
  import opened ValueMessage
  import opened KeyType
  import opened InterpMod
  import opened DiskTypesMod
  import opened AllocationMod
  import opened MsgHistoryMod
  import IndirectionTableMod
  import opened SplinterTreeMachineMod
  import Nat_Order

  // Select the messages that lookup finds.
  function LookupToMessage(lookup: TrunkPath) : (outm : Message)
    ensures outm.Define?
  {
    lookup.Decode()
  }

  predicate LookupExists(v: Variables, cache: CacheIfc.Variables, key: Key)
  {
    exists lookup :: ValidLookup(v, cache, key, lookup)
  }

  function IMLookup(v: Variables, cache: CacheIfc.Variables, key: Key) : (lookup: TrunkPath)
    requires LookupExists(v, cache, key)
    ensures ValidLookup(v, cache, key, lookup)
    ensures lookup.WF()
  {
     var lookup :| ValidLookup(v, cache, key, lookup);
     lookup
  }


  // Produce a receipt for this key
  function IMKey(v: Variables, cache: CacheIfc.Variables, key: Key) : (m: Message)
    ensures m.Define?
  {
    if LookupExists(v, cache, key) // Always true by invariant
    then
      LookupToMessage(IMLookup(v, cache, key))
    else
      DefaultMessage() // this is not a absence of a key, this case cannot happen by invariant
  }

  function IM(cache: CacheIfc.Variables, v: Variables) : (i:Interp)
  {
    RawInterp((imap key | AnyKey(key) :: IMKey(v, cache, key)), v.nextSeq) // check v.nextSeq used to be sb.endSeq
  }

  function IMStable(cache: CacheIfc.Variables, sb: Superblock) : (i:Interp)
  {
    if exists indTbl :: IndirectionTableMod.DurableAt(indTbl, cache, sb.indTbl)
    then
      var indTbl :| IndirectionTableMod.DurableAt(indTbl, cache, sb.indTbl);
      var v := Variables(indTbl, map[], sb.endSeq, Frozen.Idle, sb.root);
      IM(cache, v)
    else
      InterpMod.Empty()
  }

  // Imagine what the disk would look like if we were running and haven't
  // added any stuff to the membuffer.
  function IMNotRunning(cache: CacheIfc.Variables, sb: Superblock) : (i:Interp)
  {
    var indTbl := IndirectionTableMod.I(cache.dv, sb.indTbl);
    if indTbl.None?
     then InterpMod.Empty()
   else
      var pretendVariables := Variables(indTbl.value, map[], sb.endSeq, Idle, sb.root);
      IM(cache, pretendVariables)
  }

  predicate ValidLookupHasCU(v: Variables, cache: CacheIfc.Variables, lookup: TrunkPath, cu: CU)
  {
    && lookup.Valid(v, cache)
    && cu in lookup.CUs()
  }

  function IReads(v: Variables, cache: CacheIfc.Variables) : set<CU> {
    set cu:CU |
      && cu in CUsInDisk()
      && (exists lookup :: ValidLookupHasCU(v, cache, lookup, cu))
      :: cu
  }

  // May have to make this an invariant later.
  lemma NonEquivocate(v: Variables, cache: CacheIfc.Variables, lookup0: TrunkPath, lookup1 : TrunkPath)
    requires lookup0.k == lookup1.k
    requires lookup0.Valid(v, cache)
    requires lookup1.Valid(v, cache)
    ensures lookup0 == lookup1
  {

  }

  predicate AllLookupsExist(v: Variables, cache: CacheIfc.Variables)
  {
    forall key | AnyKey(key) :: LookupExists(v, cache, key)
  }

  lemma LookupsEquivalent(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, lookup0 : TrunkPath, lookup1: TrunkPath, count : nat)
    requires lookup0.k == lookup1.k
    requires lookup0.WF()
    requires lookup1.WF()
    requires lookup0.Valid(v, cache0)
    requires lookup1.Valid(v, cache1)
    requires count <= |lookup0.steps|
    requires count <= |lookup1.steps|
    requires DiskViewsEquivalent(cache0.dv, cache1.dv, IReads(v, cache0))
    ensures forall i :: ((0 <= i < count) ==> (lookup0.steps[i] == lookup1.steps[i]))
  {
      if 0 < count
      {
        LookupsEquivalent(v, cache0, cache1, lookup0, lookup1, count-1);
        var step0 := lookup0.steps[count-1];
        var step1 := lookup1.steps[count-1];

        if (count - 1 == 0) {
          // they share roots
          assert step0.na.id == step1.na.id;
        } else {
          // prior steps were the same, and the pivots took us to
          // the same place.
          // TODO broken here, probably because pivot lookups not defined right yet.
          assert step0.na.id == step1.na.id;
        }


        assert step0.na.id == step1.na.id;
        assert step0.na.cu == step1.na.cu;
        assert step0.na.cu in CUsInDisk();  // try to trigger set comprehension
        assert step0.na.cu in lookup0.CUs();
        assert ValidLookupHasCU(v, cache0, lookup0, step0.na.cu);
        assert step0.na.cu in IReads(v, cache0); // TRIGGER
        assert step0.na.node == step1.na.node;

        assert step0.na == step1.na;

        // XXX just playing around here; need to add a branchReceipt lemma?
        if (0 < |step0.branchReceipts|) {
          var cu0 := step0.branchReceipts[0].branchTree.Root();
          var cu1 := step1.branchReceipts[0].branchTree.Root();

          assert cu0 == cu1;
          assert CacheIfc.ReadValue(cache0, cu0) == CacheIfc.ReadValue(cache1, cu1);
        }

        assert step0.branchReceipts == step1.branchReceipts;
        assert step0 == step1 ;
      }
  }

  // TODO; Might need to change this to table about both IM and IMStable
  lemma Framing(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, sb:Superblock)
    requires DiskViewsEquivalent(cache0.dv, cache1.dv, IReads(v, cache0))
    requires AllLookupsExist(v, cache0)
    requires AllLookupsExist(v, cache1)
    // TODO: require lookup exist
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

      LookupsEquivalent(v, cache0, cache1, lookup0, lookup1, |lookup1.steps|);

      calc {
        lookup0;

        lookup1;
      }

    }
    assume false;
    assert IM(cache0, v) == IM(cache1, v);
  }

  lemma PutEffect(v: Variables, v': Variables, cache: CacheIfc.Variables, cache': CacheIfc.Variables, sb: Superblock, key: Key, value: Value, sk: Skolem)
    ensures IM(cache', v') == IM(cache, v).Put(key, Define(value))
  {
    assume false; // This is hard to prove -- we need to finish a tree
  }

  // Show that Flushes across trunk nodes preserve the invariant
  lemma FlushEffect(v: Variables, v': Variables, cache: CacheIfc.Variables, cache': CacheIfc.Variables, sb: Superblock, sk: Skolem)
    ensures IM(cache', v') == IM(cache, v)
  {
    // Prolly not needed
    forall key | AnyKey(key)
      ensures IMKey(v', cache', key) == IMKey(v, cache, key)
    {
      //var le0 := exists lookup0, value0 :: ValidLookup(v, cache, key, value0, lookup0);
      //var le1 := exists lookup1, value1 :: ValidLookup(v', cache', key, value1, lookup1);
      //assert le0 == le1;
      // if le0 {
      //
      // }
      // TODO
      assert IMKey(v', cache', key) == IMKey(v, cache, key);
    }

    assume false;
    assert IM(cache', v') == IM(cache, v);
  }

  // Show that compactions preserve the invariant
  lemma CompactionEffect(v: Variables, v': Variables, cache: CacheIfc.Variables, cache': CacheIfc.Variables, sb: Superblock, sk: Skolem)
    ensures IM(cache', v') == IM(cache, v)
  {
    assume false;
  }

  // Show that draining the memBuffer preserves the invariant
  lemma DrainMemBufferEffect(v: Variables, v': Variables, cache: CacheIfc.Variables, cache': CacheIfc.Variables, sb: Superblock, sk: Skolem)
    ensures IM(cache', v') == IM(cache, v)
  {
    assume false;
  }

  // All the SplinterTree Internal steps shouldn't affect the interpretation
  lemma InternalStepLemma(v: Variables, v': Variables, cache: CacheIfc.Variables, cache': CacheIfc.Variables, sb: Superblock, sk: Skolem)
    requires sk.FlushStep? || sk.DrainMemBufferStep? || sk.CompactBranchStep?
    ensures IM(cache', v') == IM(cache, v)
  {
    match sk {
     case FlushStep(flush: FlushRec) => {
        FlushEffect(v, v', cache, cache', sb, sk);
     }
     case DrainMemBufferStep(oldRoot: NodeAssignment, newRoot: NodeAssignment) => {
        DrainMemBufferEffect(v, v', cache, cache', sb, sk);
     }
     case CompactBranchStep(receipt: CompactReceipt) => {
        CompactionEffect(v, v', cache, cache', sb, sk);
     }
    }
  }

}
