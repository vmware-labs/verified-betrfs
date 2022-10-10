// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedBetree.i.dfy"
include "../../lib/Buckets/BoundedPivotsLib.i.dfy"
include "../Disk/GenericDisk.i.dfy"
include "Domain.i.dfy"
include "SplitRequest.i.dfy"

//	TODO: Stranded vs Reserved in the ReprBetree design
//		○ It has been established that we should not carry information into the freeze. I.e. in a freeze, we should not have to remember what's in the stranded and reserved set.
//		○ Proposed design:
//			§ Enabling condition for freeze should be that stranded set is empty. I.e. all AU's that could be free have been freed. Hence, nothing to remember here.
//			§ Moreover, AU that's are unused should also be freed (although this specified at the lower level)
//      § Finally, the reserved set does not have to be remembered, because AU's with used pages can be used to recover those pages during recovery?

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

  datatype GCStampedBetree = GCStampedBetree(
    reserved: set<Address>,
    stranded: set<Address>,
    stamped: StampedBetree   
    // todo(tony): The Repr Betree never strands addresses, since each AU will only contain one node. When that node is released,
    // that entire AU is immediately freed. i.e. the pages in that AU that were in the reserved set should also be freed.
  ) {
    function I() : StampedBetree {
      stamped
    }
  }
  
  // Copied from linkedJournal, except for InternalLabel
  datatype TransitionLabel =
      QueryLabel(endLsn: LSN, key: Key, value: Value)
    | PutLabel(puts: MsgHistory)
    | QueryEndLsnLabel(endLsn: LSN)
    | FreezeAsLabel(gcBetree: GCStampedBetree)
    // Internal-x labels refine to no-ops at the abstract spec
    | InternalAllocationsLabel(addrs: seq<Address>)
    | InternalMapGCLabel(allocations: set<Address>, freed: set<Address>)
    | InternalLabel() 
  {
    function I() : LinkedBetreeMod.TransitionLabel {
      match this {
        case QueryLabel(endLsn, key, value) => LinkedBetreeMod.QueryLabel(endLsn, key, value)
        case PutLabel(puts) => LinkedBetreeMod.PutLabel(puts)
        case QueryEndLsnLabel(endLsn) => LinkedBetreeMod.QueryEndLsnLabel(endLsn)
        case FreezeAsLabel(gcBetree) => LinkedBetreeMod.FreezeAsLabel(gcBetree.stamped)
        case InternalAllocationsLabel(addrs) => LinkedBetreeMod.InternalAllocationsLabel(addrs)
        case InternalMapGCLabel(_, _) => LinkedBetreeMod.InternalLabel()
        case InternalLabel() => LinkedBetreeMod.InternalLabel()
      }
    }
  }

  datatype Variables = Variables(
    betree: LinkedBetreeMod.Variables,
    // maps each in-repr node n to the representation of the subtree with that node as root
    repr: set<Address>,
    reserved: set<Address>,
    stranded: set<Address>)
  {
    predicate WF() {
      && betree.WF()
      && betree.linked.Acyclic()
    }
  }

  predicate Query(v: Variables, v': Variables, lbl: TransitionLabel, receipt: QueryReceipt)
  {
    && lbl.QueryLabel?
    && LinkedBetreeMod.Query(v.betree, v'.betree, lbl.I(), receipt)
    && v' == v.(
      betree := v'.betree
    )
  }

  predicate Put(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.PutLabel?
    && LinkedBetreeMod.Put(v.betree, v'.betree, lbl.I())
    && v' == v.(
      betree := v'.betree
    )
  }

  predicate QueryEndLsn(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.QueryEndLsnLabel?
    && LinkedBetreeMod.QueryEndLsn(v.betree, v'.betree, lbl.I())
    && v' == v.(
      betree := v'.betree
    )
  }

  predicate FreezeAs(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.FreezeAsLabel?
    && LinkedBetreeMod.FreezeAs(v.betree, v'.betree, lbl.I())
    // we only remember a subset of our reserved and stranded set as we freeze
    // TODO: For the tree, there is no need to remember stranded and reserved sets.
    // The enabling condition for Freeze should be that the reserved and stranded set are free.
    && lbl.gcBetree.reserved <= v.reserved
    && lbl.gcBetree.stranded <= v.stranded 
    && v' == v.(
      betree := v'.betree
    )
  }

  predicate InternalGrow(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalAllocationsLabel?
    && LinkedBetreeMod.InternalGrow(v.betree, v'.betree, lbl.I(), step.I())
    && v' == v.(
      betree := v'.betree,
      repr := v.repr + {step.newRootAddr}
    )
  }

  predicate InternalSplit(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalAllocationsLabel?
    && LinkedBetreeMod.InternalSplit(v.betree, v'.betree, lbl.I(), step.I())
    && var newAddrs := Set(step.pathAddrs) + step.newAddrs.Repr();
    && var discardAddrs := step.path.AddrsOnPath() + {step.path.Target().ChildAtIdx(step.request.childIdx).root.value};
    && v' == v.(
        betree := v'.betree,
        repr := v.repr + newAddrs - discardAddrs,
        stranded := v.stranded + discardAddrs
      )
  }

  predicate InternalFlushMemtable(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalAllocationsLabel?
    && LinkedBetreeMod.InternalFlushMemtable(v.betree, v'.betree, lbl.I(), step.I())
    && if v.betree.linked.HasRoot() then 
        v' == v.(
          betree := v'.betree,  // specified by LinkedBetreeMod.InternalFlushMemtable
          repr := v.repr + {step.newRootAddr} - {v.betree.linked.root.value},
          stranded := v.stranded + {v.betree.linked.root.value}
        )
      else
        v' == v.(
          betree := v'.betree,  // specified by LinkedBetreeMod.InternalFlushMemtable
          repr := v.repr + {step.newRootAddr}
        )
  }

  predicate InternalFlush(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalAllocationsLabel?
    && LinkedBetreeMod.InternalFlush(v.betree, v'.betree, lbl.I(), step.I())
    && var newAddrs := Set(step.pathAddrs) + {step.targetAddr, step.targetChildAddr};
    && var discardAddrs := step.path.AddrsOnPath() + {step.path.Target().ChildAtIdx(step.childIdx).root.value};
    && v' == v.(
        betree := v'.betree,
        repr := v.repr + newAddrs - discardAddrs,
        stranded := v.stranded + discardAddrs
      )
  }

  predicate InternalCompact(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalAllocationsLabel?
    && LinkedBetreeMod.InternalCompact(v.betree, v'.betree, lbl.I(), step.I())
    && var newAddrs := Set(step.pathAddrs) + {step.targetAddr};
    && var discardAddrs := step.path.AddrsOnPath();
    && v' == v.(
        betree := v'.betree,
        repr := v.repr + newAddrs - discardAddrs,
        stranded := v.stranded + discardAddrs
      )
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
    && lbl.allocations == {}
    && lbl.freed <= v.stranded
    && 0 < |lbl.freed|
    // State transition
    && v' == v.(
      stranded := v.stranded - lbl.freed
    )
  }

  // This is needed for the ReprBetree, because we only use one page per AU. Hence, for an AU,
  // a page could be in repr, while all others are in reserved. When we free that page in repr,
  // all the other pages (still in reserved set), are also freed.
  predicate InternalMapFreeReserved(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    // Enabling conditions
    && lbl.InternalMapGCLabel?
    && v.WF()
    && lbl.allocations == {}
    && lbl.freed <= v.reserved
    && 0 < |lbl.freed|
    // State transition
    && v' == v.(
      reserved := v.reserved - lbl.freed
    )
  }

  predicate InternalNoOp(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.InternalLabel?
    && v.WF()
    && v' == v
  }


  predicate Init(v: Variables, gcBetree: GCStampedBetree)
  {
    var linked := gcBetree.stamped.value;
    && linked.Acyclic()
    && linked.DiskIsTightWrtRepresentation()
    && linked.RepresentationIsDagFree()
    && v == Variables(
      LinkedBetreeMod.Variables(EmptyMemtable(gcBetree.stamped.seqEnd), linked),
      linked.Representation(),
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
