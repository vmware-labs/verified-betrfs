// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedBetree.i.dfy"
include "../../lib/Buckets/BoundedPivotsLib.i.dfy"
include "../Disk/GenericDisk.i.dfy"
include "Domain.i.dfy"

module MarshalledBetreeMod
{
  import opened BoundedPivotsLib
  import opened Buffers
  import opened DomainMod
  import opened GenericDisk
  import opened KeyType
//  import opened Lexicographic_Byte_Order
  import opened LSNMod
  import opened MemtableMod
  import opened MsgHistoryMod
  import opened Options
  import opened Sequences
  import opened StampedMod
  import opened Upperbounded_Lexicographic_Byte_Order_Impl
  import opened Upperbounded_Lexicographic_Byte_Order_Impl.Ord
  import opened ValueMessage
  import opened Maps
  import TotalKMMapMod
  import LinkedBetreeMod

  datatype TransitionLabel =
      QueryLabel(endLsn: LSN, key: Key, value: Value)
    | PutLabel(puts: MsgHistory)
    | QueryEndLsnLabel(endLsn: LSN)
    | FreezeAsLabel(frozenBetree: BetreeImage)
    | InternalLabel()
  {
    predicate WF() {
      && (FreezeAsLabel? ==> frozenBetree.WF())
    }

    function I() : LinkedBetreeMod.TransitionLabel
      requires WF()
    {
      match this
        case QueryLabel(endLsn, key, value) => LinkedBetreeMod.QueryLabel(endLsn, key, value)
        case PutLabel(puts) => LinkedBetreeMod.PutLabel(puts)
        case QueryEndLsnLabel(endLsn) => LinkedBetreeMod.QueryEndLsnLabel(endLsn)
        case FreezeAsLabel(frozenBetree) => LinkedBetreeMod.FreezeAsLabel(frozenBetree.I())
        case InternalLabel() => LinkedBetreeMod.InternalLabel()
    }
  }

  datatype BetreeSB = BetreeSB(
    root: Pointer,
    seqEnd: LSN)

  datatype BetreeImage = BetreeImage(superblock: BetreeSB, diskView: DiskView)
  {
    predicate TypeProvidesModel(typed: LinkedBetreeMod.StampedBetree) {
      && typed.value.WF()
      && superblock.root == typed.value.root
      && diskView == MarshalDisk(typed.value.diskView.entries)
      && superblock.seqEnd == typed.seqEnd
    }

    predicate HasModel() {
      exists typed :: TypeProvidesModel(typed)
    }

    predicate WF()
    {
      HasModel()
    }

    function I() : LinkedBetreeMod.StampedBetree
      requires WF()
    {
      var typed :| TypeProvidesModel(typed); typed
    }
  }

  function EmptyBetreeImage() : BetreeImage
  {
    BetreeImage(BetreeSB(None, 0), DiskView(map[]))
  }

  datatype Variables = Variables(
    betreeImage: BetreeImage,
    memtable: Memtable)
  {
    predicate WF() {
      && betreeImage.WF()
    }
  }

  function MarshalDisk(typed: map<Address, LinkedBetreeMod.BetreeNode>) : DiskView
  {
    DiskView(map addr | addr in typed :: Marshal(typed[addr]))
  }

  predicate TypeProvidesModel(v: Variables, typed: LinkedBetreeMod.Variables)
  {
    && v.betreeImage.TypeProvidesModel(Stamped(typed.linked, typed.memtable.seqEnd))
    && v.memtable == typed.memtable
  }

  predicate InitModel(v: Variables, betreeImage: BetreeImage, t: LinkedBetreeMod.Variables)
  {
    && TypeProvidesModel(v, t)
    && t.linked.Acyclic()
    && LinkedBetreeMod.Init(t, Stamped(t.linked, t.memtable.seqEnd))
    && v.betreeImage == betreeImage
//      && v.unmarshalledTail.IsEmpty() // Implied by LinkedBetree.Init && TypeProvidesModel.
  }

  predicate Init(v: Variables, betreeImage: BetreeImage)
  {
    (exists t :: InitModel(v, betreeImage, t))
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.WF()
    && (exists t, t' ::
      && TypeProvidesModel(v, t)
      && TypeProvidesModel(v', t')
      && LinkedBetreeMod.Next(t, t', lbl.I())
    )
  }
}
