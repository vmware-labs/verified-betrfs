// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedBetree.i.dfy"
include "../../lib/Buckets/BoundedPivotsLib.i.dfy"
include "../Journal/GenericDisk.i.dfy"
include "Domain.i.dfy"
include "SplitRequest.i.dfy"

module ReprBetree
{
  import opened BoundedPivotsLib
  import opened Buffers
  import opened DomainMod
  import opened LSNMod
  import opened ValueMessage
  import opened GenericDisk
  import opened KeyType
  import opened MemtableMod
  import opened MsgHistoryMod
  import opened Sequences
  import opened SplitRequestMod
  import LinkedBetreeMod

  type Pointer = GenericDisk.Pointer
  type Address = GenericDisk.Address

  type StampedBetree = LinkedBetreeMod.StampedBetree
  type LinkedBetree = LinkedBetreeMod.LinkedBetree
  type Path = LinkedBetreeMod.Path
  type PathAddrs = LinkedBetreeMod.PathAddrs
  type SplitAddrs = LinkedBetreeMod.SplitAddrs
  type QueryReceipt = LinkedBetreeMod.QueryReceipt

  datatype GCBetree = GCBetree(
    reserved: seq<Address>,
    stranded: set<Address>,
    stamped: StampedBetree
  )
  
  // Copied from linkedJournal, except for InternalLabel
  datatype TransitionLabel =
      QueryLabel(endLsn: LSN, key: Key, value: Value)
    | PutLabel(puts: MsgHistory)
    | QueryEndLsnLabel(endLsn: LSN)
    | FreezeAsLabel(gcBetree: GCBetree)
    // Internal-x labels refine to no-ops at the abstract spec
    | InternalMapGCLabel(allocations: seq<Address>, freed: set<Address>)
    | InternalLabel() 
  {
    function I() : LinkedBetreeMod.TransitionLabel {
      match this {
        case QueryLabel(endLsn, key, value) => LinkedBetreeMod.QueryLabel(endLsn, key, value)
        case PutLabel(puts) => LinkedBetreeMod.PutLabel(puts)
        case QueryEndLsnLabel(endLsn) => LinkedBetreeMod.QueryEndLsnLabel(endLsn)
        case FreezeAsLabel(gcBetree) => LinkedBetreeMod.FreezeAsLabel(gcBetree.stamped)
        case InternalMapGCLabel(_, _) => LinkedBetreeMod.InternalLabel()
        case InternalLabel() => LinkedBetreeMod.InternalLabel()
      }
    }
  }

  datatype Variables = Variables(
    betree: LinkedBetreeMod.Variables,
    // maps each in-repr node n to the representation of the subtree with that node as root
    repr: set<Address>,
    reserved: seq<Address>,
    stranded: set<Address>)
  {
    predicate WF() {
      betree.WF()
    }
  }

  predicate Query(v: Variables, v': Variables, lbl: TransitionLabel, receipt: QueryReceipt)
  {
    && LinkedBetreeMod.Query(v.betree, v'.betree, lbl.I(), receipt)
    && v' == v.(
      betree := v'.betree
    )
  }

  predicate Put(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && LinkedBetreeMod.Put(v.betree, v'.betree, lbl.I())
    && v' == v.(
      betree := v'.betree
    )
  }

  predicate QueryEndLsn(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && LinkedBetreeMod.QueryEndLsn(v.betree, v'.betree, lbl.I())
    && v' == v.(
      betree := v'.betree
    )
  }

  predicate FreezeAs(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && LinkedBetreeMod.FreezeAs(v.betree, v'.betree, lbl.I())
    // we only remember a subset of our reserved and stranded set as we freeze
    && IsPrefix(lbl.gcBetree.reserved, v.reserved)
    && lbl.gcBetree.stranded <= v.stranded 
    && v' == v.(
      betree := v'.betree
    )
  }

  predicate InternalGrow(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && LinkedBetreeMod.InternalGrow(v.betree, v'.betree, lbl.I(), step.I())
    && v' == v.(
      betree := v'.betree,
      repr := v.repr + {step.newRootAddr}
    )
  }

  predicate InternalSplit(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    // TODO
    false
  }

  predicate InternalFlushMemtable(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    // TODO
    false
  }

  predicate InternalFlush(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    // TODO
    false
  }

  predicate InternalCompact(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    // TODO
    false
  }

  predicate InternalMapReserve(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    // Enabling conditions
    && lbl.InternalMapGCLabel?
    && v.WF()
    && 0 < |lbl.allocations|
    && lbl.freed == {}
    // State transition
    && v' == v.(
      reserved := v.reserved + lbl.allocations
    )
  }

  predicate InternalMapFree(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    // Enabling conditions
    && lbl.InternalMapGCLabel?
    && v.WF()
    && lbl.allocations == []
    && lbl.freed <= v.stranded
    && 0 < |lbl.freed|
    // State transition
    && v' == v.(
      stranded := v.stranded - lbl.freed
    )
  }

  predicate InternalNoOp(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.InternalLabel?
    && v.WF()
    && v' == v
  }

  predicate Init(v: Variables, gcBetree: GCBetree)
  {
    && v.betree.linked.Acyclic()
    && v == Variables(
      LinkedBetreeMod.Variables(EmptyMemtable(gcBetree.stamped.seqEnd), gcBetree.stamped.value),
      v.betree.linked.ReachableAddrs(),
      gcBetree.reserved,
      gcBetree.stranded
    )
  }

  datatype Step =
      QueryStep(receipt: QueryReceipt)
    | PutStep()
    | QueryEndLsnStep()
    | FreezeAsStep()
    | InternalGrowStep(newRootAddr: Address)
    | InternalSplitStep(path: Path, request: SplitRequest, newAddrs: SplitAddrs, pathAddrs: PathAddrs)
    | InternalFlushMemtableStep(newRootAddr: Address)
    | InternalFlushStep(path: Path, childIdx: nat, targetAddr: Address, targetChildAddr: Address, pathAddrs: PathAddrs)
    | InternalCompactStep(path: Path, compactedBuffers: BufferStack, targetAddr: Address, pathAddrs: PathAddrs)
    | InternalMapReserveStep()    // reserve more addresses from the global allocator
    | InternalMapFreeStep()       // free some stranded addresses
    | InternalNoOpStep()
  {
    function I() : LinkedBetreeMod.Step {
      match this {
        case QueryStep(receipt) => LinkedBetreeMod.QueryStep(receipt)
        case PutStep() => LinkedBetreeMod.PutStep()
        case QueryEndLsnStep() => LinkedBetreeMod.QueryEndLsnStep()
        case FreezeAsStep() => LinkedBetreeMod.FreezeAsStep()
        case InternalGrowStep(newRootAddr) => LinkedBetreeMod.InternalGrowStep(newRootAddr)
        case InternalSplitStep(path, reqeust, newAddrs, pathAddrs) => 
              LinkedBetreeMod.InternalSplitStep(path, reqeust, newAddrs, pathAddrs)
        case InternalFlushStep(path, childIdx, targetAddr, targetChildAddr, pathAddrs) => 
              LinkedBetreeMod.InternalFlushStep(path, childIdx, targetAddr, targetChildAddr, pathAddrs)
        case InternalFlushMemtableStep(newRootAddr) => LinkedBetreeMod.InternalFlushMemtableStep(newRootAddr)
        case InternalCompactStep(path, compactedBuffers, targetAddr, pathAddrs) => LinkedBetreeMod.InternalCompactStep(path, compactedBuffers, targetAddr, pathAddrs)
        case InternalMapReserveStep() => LinkedBetreeMod.InternalNoOpStep()
        case InternalMapFreeStep() => LinkedBetreeMod.InternalNoOpStep()
        case InternalNoOpStep() => LinkedBetreeMod.InternalNoOpStep()
      }
    }
  }

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case QueryStep(receipt) => Query(v, v', lbl, receipt)
      case PutStep() => Put(v, v', lbl)
      case QueryEndLsnStep() => QueryEndLsn(v, v', lbl)
      case FreezeAsStep() => FreezeAs(v, v', lbl)
      case InternalGrowStep(_) => InternalGrow(v, v', lbl, step)
      case InternalSplitStep(_, _, _, _) => InternalSplit(v, v', lbl, step)
      case InternalFlushStep(_, _, _, _, _) => InternalFlush(v, v', lbl, step)
      case InternalFlushMemtableStep(_) => InternalFlushMemtable(v, v', lbl, step)
      case InternalCompactStep(_, _, _, _) => InternalCompact(v, v', lbl, step)
      case InternalMapReserveStep() => InternalMapReserve(v, v', lbl)
      case InternalMapFreeStep() => InternalMapFree(v, v', lbl)
      case InternalNoOpStep() => InternalNoOp(v, v', lbl)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }

}
