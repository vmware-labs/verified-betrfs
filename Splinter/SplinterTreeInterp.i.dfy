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

  datatype LookupRecord = LookupRecord(
    //cu: CU
    // If we want to use trunk paths, I'm missing a case where the lookup is in the memtable CheckMemtable
    key : Key,
    path : Option<TrunkPath>,
    memBuffer : map<Key, Message>
  )
  type Lookup = LookupRecord //seq<LookupRecord>

  // A valid lookup is something that produces a non DefaultMessage from the membuffer or has a valid trunk path
  // in the splinter tree
  predicate ValidLookup(v: Variables, cache: CacheIfc.Variables, key: Key, lookup: Lookup) {
    exists value :: ( && lookup.key == key
                      && lookup.memBuffer == v.memBuffer
                      && var inMemBuffer := CheckMemtable(v, key, value);
                      && ( || inMemBuffer
                           || (lookup.path.Some? ==> checkSpinterTree(v, cache, key, value, lookup.path.value))
                         )
                    )
  }

  // Select the messages that lookup finds.
  function LookupToMessage(lookup: Lookup) : (outm : Message)
    ensures outm.Define?
  {
    var path := lookup.path;
    if lookup.key in lookup.memBuffer
    then
      var msg := MsgSeqMod.CombineDeltasWithDefine([lookup.memBuffer[lookup.key]]);
      if msg.Some?
      then
        msg.value
      else
        DefaultMessage()
    else if path.Some?
    then
       path.value.Decode()
    else
       DefaultMessage()
  }

  // Produce a receipt for this key
  function IMKey(v: Variables, cache: CacheIfc.Variables, key: Key) : (m: Message)
    ensures m.Define?
  {
    if exists lookup :: ValidLookup(v, cache, key, lookup) // Always true by invariant
    then
      var lookup :| ValidLookup(v, cache, key, lookup);
      LookupToMessage(lookup)
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

  function IReadsKey(v: Variables, cache: CacheIfc.Variables, sb: Superblock, key: Key) : set<CU> {
    if exists lookup :: ValidLookup(v, cache, key, lookup)
    then
      var lookup :| ValidLookup(v, cache, key, lookup);
      set i | lookup.path.Some? && i in lookup.path.value.CUs()
      //set i | 0<=i<|lookup| :: var lr:LookupRecord := lookup[i]; lr.cu
    else
      {}
  }

  function IReadsSet(v: Variables, cache: CacheIfc.Variables, sb: Superblock) : set<CU> {
    set cu:CU |
      && cu in CUsInDisk()
      && exists key :: cu in IReadsKey(v, cache, sb, key)
  }

  // What do we need this for -- we already have IReadsSet ??
  function IReads(v: Variables, cache: CacheIfc.Variables, sb: Superblock) : (result : seq<CU>)
    // commenting for now
    //ensures forall cu :: cu in result <==> cu in IReadsSet(v, cache, sb)
  {
    // TODO: CU's or nats it doesn't know how to sort it. We need to fix it
    //var iReadSet := IReadsSet(v, cache, sb);
    //var iReadSeq := Nat_Order.SortSet(IReadsSet(v, cache, sb));
    //assert (forall cu :: cu in iReadSet ==> cu in iReadSet);
    //assert (forall cu :: cu in iReadSet ==> cu in iReadSeq);
    []
  }

  // TODO; Might need to change this to table about both IM and IMStable
  lemma Framing(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, sb:Superblock)
    requires DiskViewsEquivalentForSet(cache0.dv, cache1.dv, IReads(v, cache0, sb))
    ensures IM(cache0, v) == IM(cache1, v)
  {
    // TODO I'm surprised this proof passes easily.
    // narrator: It doesn't.
    // Sowmya : Plot twist .. Now it times out :)
    // It doesn't after I changed lookups to account for the memBuffer
    // TODO: Check the Implementation of lookup
    forall key | AnyKey(key)
      ensures IMKey(v, cache0, key) == IMKey(v, cache1, key)
    {
      var le0 := exists lookup0 :: ValidLookup(v, cache0, key, lookup0);
      var le1 := exists lookup1 :: ValidLookup(v, cache1, key, lookup1);
      if le0 {
        var lookup0 :| ValidLookup(v, cache0, key, lookup0);
        assume ValidLookup(v, cache1, key, lookup0);
      }
      if le1 {
        var lookup1 :| ValidLookup(v, cache1, key, lookup1);
        assume ValidLookup(v, cache0, key, lookup1);
      }
      assert le0 == le1;
      if (le0) {
        // This definitely won't work.
        var lookup0 :| ValidLookup(v, cache0, key, lookup0);
        var lookup1 :| ValidLookup(v, cache1, key, lookup1);
        calc {
          IMKey(v, cache0, key);
            { assume false; } // var|
          LookupToMessage(lookup0);
            { assume false; } // framing
          LookupToMessage(lookup1);
            { assume false; } // var|
          IMKey(v, cache1, key);
        }
      } else {
        calc {
          IMKey(v, cache0, key);
          DefaultMessage();
          IMKey(v, cache1, key);
        }
      }
    }
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
    assume false;
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
