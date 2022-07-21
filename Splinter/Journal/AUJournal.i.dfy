// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "ReprJournal.i.dfy"

// A Journal that keeps an in-memory index that maps each in-use LSN to the AUs that store it.
// The impl will keep such an index so that Discard can return freed AUs without having to
// fault in the freed section of the journal to learn the chain of AUs involved.

module AUJournal {
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import opened Maps
  import Mathematics
  import ReprJournal
  import opened GenericDisk

  function AddrsForAu(au: AU) : (out: seq<Address>)
  {
    seq(PageCount(), page requires 0 <= page < PageCount() => Address(au, page))
  }

  function AddrsForAusDefn(aus: seq<AU>) : (out: seq<Address>)
  {
    if |aus| == 0 then []
    else AddrsForAusDefn(DropLast(aus)) + AddrsForAu(Last(aus))
  }

  lemma AddrsForAusInduction(aus: seq<AU>)
    ensures forall addr:Address :: addr.au in aus && addr.WF() <==> addr in AddrsForAusDefn(aus)
  {
    if 0 < |aus| {
      AddrsForAusInduction(DropLast(aus));
      forall addr:Address | addr.au in aus && addr.WF() ensures addr in AddrsForAusDefn(aus) {
        assert AddrsForAu(addr.au)[addr.page] == addr;
      }
    }
  }

  function AddrsForAus(aus: seq<AU>) : (out: seq<Address>)
    ensures forall addr:Address :: addr.au in aus && addr.WF() <==> addr in AddrsForAusDefn(aus)
  {
    AddrsForAusInduction(aus);
    AddrsForAusDefn(aus)
  }

  // Well-formed if we have exactly one of a nextReserved address or a fresh au
  // coming in from the transition label; computes the current address (from
  // either source) and the next address to record as reserved.
  datatype NextAddrTool = NextAddrTool(nextReserved: Option<Address>, au: Option<AU>)
  {
    predicate WF()
    {
      nextReserved.Some? <==> au.None?
    }

    function Cur() : Address
      requires WF()
    {
      if nextReserved.Some? then nextReserved.value else Address(au.value, 0)
    }

    function Next() : Option<Address>
      requires WF()
    {
      var nextPage := Cur().page + 1;
      if nextPage < PageCount() then Some(Address(Cur().au, nextPage)) else None
    }
  }

  datatype TransitionLabel =
      ReadForRecoveryLabel(messages: MsgHistory)
    | FreezeForCommitLabel(frozenJournal: TruncatedJournal)
    | QueryEndLsnLabel(endLsn: LSN)
    | PutLabel(messages: MsgHistory)
    | DiscardOldLabel(startLsn: LSN, requireEnd: LSN, freedAUs: seq<AU>)
    | InternalLabel(au: Option<AU>)
  {
    predicate WF() {
      && (FreezeForCommitLabel? ==> frozenJournal.Decodable())
    }

    function I(marshalAddr: Option<Address>): ReprJournal.TransitionLabel
      requires (InternalLabel? <==> marshalAddr.Some?)
    {
      match this {
        case ReadForRecoveryLabel(messages) => ReprJournal.ReadForRecoveryLabel(messages)
        case FreezeForCommitLabel(frozenJournal) => ReprJournal.FreezeForCommitLabel(frozenJournal)
        case QueryEndLsnLabel(endLsn) => ReprJournal.QueryEndLsnLabel(endLsn)
        case PutLabel(messages) => ReprJournal.PutLabel(messages)
        case DiscardOldLabel(startLsn, requireEnd, freedAUs) => ReprJournal.DiscardOldLabel(startLsn, requireEnd, AddrsForAus(freedAUs))
        case InternalLabel(au) => ReprJournal.InternalLabel(marshalAddr.value)
      }
    }
  }

  type DiskView = ReprJournal.DiskView
  type TruncatedJournal = ReprJournal.TruncatedJournal
  type Step = ReprJournal.Step

  datatype Variables = Variables(
    reprJournal: ReprJournal.Variables,
    nextReserved: Option<Address>
  )
  {
    predicate WF() {
      && reprJournal.WF()
    }
  }

  predicate InternalJournalMarshal(v: Variables, v': Variables, lbl: TransitionLabel, cut: LSN)
  {
    && v.WF()
    && lbl.InternalLabel?
    && var tool := NextAddrTool(v.nextReserved, lbl.au);
    && tool.WF()
    && ReprJournal.InternalJournalMarshal(v.reprJournal, v'.reprJournal, lbl.I(Some(tool.Cur())), cut)
    && v' == v.(
      reprJournal := v'.reprJournal,
      nextReserved := tool.Next()
    )
  }

}
