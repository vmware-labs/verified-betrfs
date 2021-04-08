include "../lib/Base/total_order.i.dfy"
include "Tables.i.dfy"
include "MsgSeq.i.dfy"

module BetreeMachineMod {
  import opened Options
  import opened MessageMod
  import opened InterpMod
  import opened AllocationMod
  import opened MsgSeqMod
  import opened IndirectionTableMod
  import CacheIfc

  datatype Superblock = Superblock(
    itbl: IndirectionTableMod.Superblock,
    rootIdx: IndirectionTableMod.IndirectionTable,
    seqEnd: nat)

  datatype Variables = Variables()

  predicate Query(v: Variables, v': Variables, key: Key, value: Value)
  {
    && true //TODO
    && v' == v
  }

  predicate Put(v: Variables, v': Variables, key: Key, value: Value)
  {
    && true //TODO
    && v' == v
  }

  predicate Internal(v: Variables, v': Variables)
  {
    false
  }

  predicate CommitStart(v: Variables, v': Variables, cache: CacheIfc.Variables, sb: Superblock, newBoundaryLSN: LSN)
  {
    && true //TODO
  }

  predicate CommitComplete(s: Variables, s': Variables, cache: CacheIfc.Variables, sb: Superblock)
  {
    && true //TODO
  }
}

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
  function LookupToValue(lookup: Lookup) : Value
    // TODO body

  predicate ValidLookup(dv: DiskView, itbl: IndirectionTableMod.IndirectionTable, key: Key, lookup: Lookup)
    // TODO

  function IMKey(dv: DiskView, sb: Superblock, key: Key) : Value
  {
    var itbl := IndirectionTableMod.I(dv, sb.itbl);
    if
      && itbl.Some?
      && exists lookup :: ValidLookup(dv, itbl.value, key, lookup)
    then
      var lookup :| ValidLookup(dv, itbl.value, key, lookup);
      LookupToValue(lookup)
    else
      DefaultValue()
  }

  function IM(dv: DiskView, sb: Superblock) : (i:Interp)
    ensures i.WF()
  {
    Interp(imap key | key in AllKeys() :: IMKey(dv, sb, key), sb.seqEnd)
  }

  function IReadsKey(dv: DiskView, itbl: Option<IndirectionTableMod.IndirectionTable>, key: Key) : set<AU> {
    
    if
      && itbl.Some?
      && exists lookup :: ValidLookup(dv, itbl.value, key, lookup)
    then
      var lookup :| ValidLookup(dv, itbl.value, key, lookup);
      set i | 0<=i<|lookup| :: var lr:LookupRecord := lookup[i]; lr.cu.au
    else
      {}
  }

  function IReadsSet(dv: DiskView, sb: Superblock) : set<AU> {
    var itbl := IndirectionTableMod.I(dv, sb.itbl);
    set au:AU |
      && au < AUSizeInCUs()
      && exists key :: au in IReadsKey(dv, itbl, key)
  }

  function IReads(dv: DiskView, sb: Superblock) : seq<AU>
    ensures forall au :: au in IReads(dv, sb) <==> au in IReadsSet(dv, sb)
  {
    Nat_Order.SortSet(IReadsSet(dv, sb))
  }

  lemma Framing(sb:Superblock, dv0: DiskView, dv1: DiskView)
    requires forall cu:CU :: cu.au in IReads(dv0, sb) ==>
      && cu in dv0
      && cu in dv1
      && dv0[cu]==dv1[cu]
    ensures IM(dv0, sb) == IM(dv1, sb)
  {
    // TODO I'm surprised this proof passes easily.
    // narrator: It doesn't.
    forall key | key in AllKeys()
      ensures IMKey(dv0, sb, key) == IMKey(dv1, sb, key)
    {
      var itbl0 := IndirectionTableMod.I(dv0, sb.itbl);
      var itbl1 := IndirectionTableMod.I(dv1, sb.itbl);
      if itbl0.Some? && itbl1.Some?
      {
        var le0 := exists lookup0 :: ValidLookup(dv0, itbl0.value, key, lookup0);
        var le1 := exists lookup1 :: ValidLookup(dv1, itbl1.value, key, lookup1);
        if le0 {
          var lookup0 :| ValidLookup(dv0, itbl0.value, key, lookup0);
          assume ValidLookup(dv1, itbl1.value, key, lookup0);
        }
        if le1 {
          var lookup1 :| ValidLookup(dv1, itbl1.value, key, lookup1);
          assume ValidLookup(dv0, itbl1.value, key, lookup1);
        }
        assert le0 == le1;
        if (le0) {
          // This definitely won't work.
          var lookup0 :| ValidLookup(dv0, itbl0.value, key, lookup0);
          var lookup1 :| ValidLookup(dv1, itbl1.value, key, lookup1);
          calc {
            IMKey(dv0, sb, key);
              { assume false; } // var|
            LookupToValue(lookup0);
              { assume false; } // framing
            LookupToValue(lookup1);
              { assume false; } // var|
            IMKey(dv1, sb, key);
          }
        } else {
          calc {
            IMKey(dv0, sb, key);
            DefaultValue();
            IMKey(dv1, sb, key);
          }
        }
      }
    }
  }
}
