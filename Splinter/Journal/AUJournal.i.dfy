// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "ReprJournal.i.dfy"
include "../Disk/AUDisk.i.dfy"

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
  import opened AUDisk = GenericDisk(AUAddress)
  import AUReprJournal = ReprJournal(AUAddress)
  import AUAddress

  type AU = AUAddress.AU

  type Pointer = AUDisk.Pointer
  type Address = AUDisk.Address

  function AddrsForAus(aus: seq<AU>) : seq<AUReprJournal.Address>
  {
    []  // TODO
    //seq(|aus|*AUAddress.PageSize(), i:nat requires i<|aus|*AUAddress.PageSize() => aus[i]
  }

  datatype TransitionLabel =
      ReadForRecoveryLabel(messages: MsgHistory)
    | FreezeForCommitLabel(frozenJournal: TruncatedJournal)
    | QueryEndLsnLabel(endLsn: LSN)
    | PutLabel(messages: MsgHistory)
    | DiscardOldLabel(startLsn: LSN, requireEnd: LSN, freedAddrs: seq<AU>)
    | InternalLabel(au: Option<AU>)
  {
    predicate WF() {
      && (FreezeForCommitLabel? ==> frozenJournal.Decodable())
    }

    function I(nextReserved: Option<AUAddress.Address>): AUReprJournal.TransitionLabel
      requires InternalLabel? && au.None? ==> nextReserved.Some?
    {
      match this {
        case ReadForRecoveryLabel(messages) => AUReprJournal.ReadForRecoveryLabel(messages)
        case FreezeForCommitLabel(frozenJournal) => AUReprJournal.FreezeForCommitLabel(frozenJournal)
        case QueryEndLsnLabel(endLsn) => AUReprJournal.QueryEndLsnLabel(endLsn)
        case PutLabel(messages) => AUReprJournal.PutLabel(messages)
        case DiscardOldLabel(startLsn, requireEnd, freedAddrs) => AUReprJournal.DiscardOldLabel(startLsn, requireEnd, AddrsForAus(freedAddrs))
        case InternalLabel(au) => AUReprJournal.InternalLabel(
            var x:AUReprJournal.Address := match au {
              case Some(au) => AUAddress.Address(au, 0)
              case None => nextReserved.value
            }; x
          )
      }
    }
  }

  type DiskView = AUReprJournal.DiskView
  type TruncatedJournal = AUReprJournal.TruncatedJournal
  type Step = AUReprJournal.Step

  datatype Variables = Variables(
    reprJournal: AUReprJournal.Variables,
    nextReserved: Option<AUAddress.Address>
  )
  {
    predicate WF() {
      && reprJournal.WF()
    }
  }

  predicate InternalJournalMarshal(v: Variables, v': Variables, lbl: TransitionLabel, cut: LSN)
  {
    && v.WF()
    && AUReprJournal.InternalJournalMarshal(v.reprJournal, v'.reprJournal, lbl.I(v.nextReserved), cut)
    && var addr := if v.nextReserved.Some? then v.nextReserved.value else AUAddress.Address(lbl.au.value, 0);
    && v' == v.(
      reprJournal := v'.reprJournal
      //,
      //nextReserved -> increment or None?
    )
  }

}
