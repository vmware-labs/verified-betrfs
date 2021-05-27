// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/total_order.i.dfy"
include "Tables.i.dfy"
include "MsgSeq.i.dfy"
include "Betree.i.dfy"
include "Message.s.dfy"
include "Interp.s.dfy"

// interpretation for the Betree Implementation
module BetreeInterpMod {
  import opened Options
  import opened MessageMod
  import opened InterpMod
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

  // What indirection table would we see if the system were running?
  function ITbl(v: Variables, cache: CacheIfc.Variables, sb: Superblock) : Option<IndirectionTableMod.IndirectionTable> {
    // match v {
    //   case Starting => IndirectionTableMod.I(cache.dv /*TODO change ind tbl to expect cache*/, sb.indTbl)
    //   case Running => Some(v.indTbl)
    // }
    // TODO figure out the interpretation split here
    Some(v.indTbl)
  }

  function IMKey(v: Variables, cache: CacheIfc.Variables, sb: Superblock, key: Key) : Message
  {
    var indTbl := ITbl(v, cache, sb);
    if
      && indTbl.Some?
      && exists lookup :: ValidLookup(v, cache, key, lookup)
    then
      var lookup :| ValidLookup(v, cache, key, lookup);
      LookupToMessage(lookup)
    else
      MessagePut(key, DefaultValue())
  }

  function IM(v: Variables, cache: CacheIfc.Variables, sb: Superblock) : (i:Interp)
    ensures i.WF()
  {
    Interp(imap key | key in AllKeys() :: IMKey(v, cache, sb, key), sb.endSeq)
  }

  function IReadsKey(v: Variables, cache: CacheIfc.Variables, sb: Superblock, key: Key) : set<CU> {
    var indTbl := ITbl(v, cache, sb);
    if
      && indTbl.Some?
      && exists lookup :: ValidLookup(v, cache, key, lookup)
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

  lemma Framing(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, sb:Superblock)
    requires DiskViewsEquivalentForSet(cache0.dv, cache1.dv, IReads(v, cache0, sb))
    ensures IM(v, cache0, sb) == IM(v, cache1, sb)
  {
    // TODO I'm surprised this proof passes easily.
    // narrator: It doesn't.
    forall key | key in AllKeys()
      ensures IMKey(v, cache0, sb, key) == IMKey(v, cache1, sb, key)
    {
      var indTbl0 := ITbl(v, cache0, sb);
      var indTbl1 := ITbl(v, cache1, sb);
      if indTbl0.Some? && indTbl1.Some?
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
            IMKey(v, cache0, sb, key);
              { assume false; } // var|
            LookupToValue(lookup0);
              { assume false; } // framing
            LookupToValue(lookup1);
              { assume false; } // var|
            IMKey(v, cache1, sb, key);
          }
        } else {
          calc {
            IMKey(v, cache0, sb, key);
            DefaultValue();
            IMKey(v, cache1, sb, key);
          }
        }
      }
    }
  }

  lemma PutEffect(v: Variables, v': Variables, cache: CacheIfc.Variables, cache': CacheIfc.Variables, sb: Superblock, key: Key, value: Value, sk: Skolem)
    ensures IM(v', cache', sb) == IM(v, cache, sb).Put(key, MessagePut(key, value))
  {
    assume false; // This is hard to prove -- we need to finish a tree
  }
}
