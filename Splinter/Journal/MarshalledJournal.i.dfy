// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/AbstractJournal.i.dfy"
include "LinkedJournal.i.dfy"

module MarshalledJournal {
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import opened JournalLabels
  import opened Maps
  import LinkedJournal

  type Block(!new, ==)
  function Parse<T>(block: Block) : T
  function Marshal<T>(t: T) : Block
  lemma ParseAxiom<T>(t: T)
    ensures Parse(Marshal(t)) == t

  type Address = LinkedJournal.Address
  type Pointer = LinkedJournal.Pointer
  type Disk = map<Address, Block>

  datatype Variables = Variables(
    disk: Disk,
    freshestRec: Pointer,
    boundaryLSN: LSN,
    unmarshalledTail: MsgHistory)

  function MarshalDisk(typed: map<Address, LinkedJournal.JournalRecord>) : Disk
  {
    map addr | addr in typed :: Marshal(typed[addr])
  }

  predicate TypeProvidesModel(v: Variables, typed: LinkedJournal.Variables)
  {
    && typed.unmarshalledTail == v.unmarshalledTail 
    && typed.truncatedJournal.freshestRec == v.freshestRec
    && MarshalDisk(typed.truncatedJournal.diskView.entries) == v.disk
    && typed.truncatedJournal.diskView.boundaryLSN == v.boundaryLSN
  }

  predicate Init(v: Variables, tj: LinkedJournal.TruncatedJournal)
  {
    (exists t ::
      && TypeProvidesModel(v, t)
      && LinkedJournal.Init(t, tj)
    )
  }

  predicate Inv(v: Variables) {
    && (exists typed :: TypeProvidesModel(v, typed))
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    (exists t, t' ::
      && TypeProvidesModel(v, t)
      && TypeProvidesModel(v', t')
      && LinkedJournal.Next(t, t', lbl)
    )
  }
}
