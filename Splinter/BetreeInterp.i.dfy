// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/total_order.i.dfy"
include "IndirectionTable.i.dfy"
include "AllocationTable.i.dfy"
include "AllocationTableMachine.i.dfy"
include "MsgSeq.i.dfy"
include "Betree.i.dfy"
include "Message.s.dfy"
include "Interp.s.dfy"

// interpretation for the Betree Implementation
module BetreeInterpMod {
  import opened Options
  import opened MessageMod
  import opened InterpMod
  import opened DiskTypesMod
  import opened AllocationMod
  import opened MsgSeqMod
  import IndirectionTableMod
  import opened BetreeMachineMod
  import Nat_Order

  datatype LookupRecord = LookupRecord(
    cu: CU
  )
  type Lookup = seq<LookupRecord>

  // Select the messages that lookup finds.
  function LookupToMessage(lookup: Lookup) : Message
    // TODO body

  predicate ValidLookup(v: Variables, cache: CacheIfc.Variables, key: Key, lookup: Lookup)
    // TODO

  // Produce a receipt for this key
  function IMKey(v: Variables, cache: CacheIfc.Variables, key: Key) : Message
  {
    if exists lookup :: ValidLookup(v, cache, key, lookup) // Always true by invariant
    then
      var lookup :| ValidLookup(v, cache, key, lookup);
      LookupToMessage(lookup)
    else
      MessagePut(key, DefaultValue()) // this is not a absence of a key, this case cannot happen by invariant
  }

  function IM(cache: CacheIfc.Variables, v: Variables) : (i:Interp)
    ensures i.WF()
  {
    Interp(imap key | key in AllKeys() :: IMKey(v, cache, key), v.nextSeq) // check v.nextSeq used to be sb.endSeq
  }

  function IMStable(cache: CacheIfc.Variables, sb: Superblock) : (i:Interp)
    ensures i.WF()
  {
    if exists indTbl :: IndirectionTableMod.DurableAt(indTbl, cache, sb.indTbl)
    then
      var indTbl :| IndirectionTableMod.DurableAt(indTbl, cache, sb.indTbl);
      var v := Variables(indTbl, map[], sb.endSeq, Frozen.Idle);
      IM(cache, v)
    else
      InterpMod.Empty()
  }

  // Imagine what the disk would look like if we were running and haven't
  // added any stuff to the membuffer.
  function IMNotRunning(cache: CacheIfc.Variables, sb: Superblock) : (i:Interp)
     ensures i.WF()
   {
     var indTbl := IndirectionTableMod.I(cache.dv, sb.indTbl);
     if indTbl.None?
      then InterpMod.Empty()
    else
       var pretendVariables := Variables(indTbl.value, map[], sb.endSeq, Idle);
       IM(cache, pretendVariables)
   }

  function IReadsKey(v: Variables, cache: CacheIfc.Variables, sb: Superblock, key: Key) : set<CU> {
    if exists lookup :: ValidLookup(v, cache, key, lookup)
    then
      var lookup :| ValidLookup(v, cache, key, lookup);
      set i | 0<=i<|lookup| :: var lr:LookupRecord := lookup[i]; lr.cu
    else
      {}
  }

  function IReadsSet(v: Variables, cache: CacheIfc.Variables, sb: Superblock) : set<CU> {
    set cu:CU |
      && cu in CUsInDisk()
      && exists key :: cu in IReadsKey(v, cache, sb, key)
  }

  function IReads(v: Variables, cache: CacheIfc.Variables, sb: Superblock) : seq<CU>
    ensures forall cu :: cu in IReads(v, cache, sb) <==> cu in IReadsSet(v, cache, sb)
  {
    // TODO: CU's or nats it doesn't know how to sort it. We need to fix it
    // Nat_Order.SortSet(IReadsSet(v, cache, sb))
    []
  }

  // TODO; Might need to change this to table about both IM and IMStable
  lemma Framing(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, sb:Superblock)
    requires DiskViewsEquivalentForSet(cache0.dv, cache1.dv, IReads(v, cache0, sb))
    ensures IM(cache0, v) == IM(cache1, v)
  {
    // TODO I'm surprised this proof passes easily.
    // narrator: It doesn't.
    forall key | key in AllKeys()
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
          MessagePut(key, DefaultValue());
          IMKey(v, cache1, key);
        }
      }
    }
  }

  lemma PutEffect(v: Variables, v': Variables, cache: CacheIfc.Variables, cache': CacheIfc.Variables, sb: Superblock, key: Key, value: Value, sk: Skolem)
    ensures IM(cache', v') == IM(cache, v).Put(key, MessagePut(key, value))
  {
    assume false; // This is hard to prove -- we need to finish a tree
  }
}
