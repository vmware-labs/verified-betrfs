// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/CrashTolerantMap.i.dfy"
include "CoordinationBetree.i.dfy"
include "AllocationBetreeRefinement.i.dfy"
include "../Betree/LikesBetreeRefinement.i.dfy"
include "../Betree/BranchedBetreeRefinement.i.dfy"
include "../Betree/LinkedBetreeRefinement.i.dfy"
include "../Betree/FilteredBetreeRefinement.i.dfy"
include "../Betree/PivotBetreeRefinement.i.dfy"
include "../Betree/PagedBetreeRefinement.i.dfy"

module FullStackBetreeRefinement {
  import opened Maps
  import opened Options
  import opened StampedMod
  import CoordinationBetree
  import AllocationBetreeMod
  import AllocationBetreeRefinement
  import AllocationBranchMod
  import CompactorMod
  import LikesBetreeRefinement
  import BranchedBetreeRefinement
  import BranchedBetreeMod
  import LinkedBetreeRefinement
  import FilteredBetreeRefinement
  import PivotBetreeRefinement
  import PagedBetreeRefinement
  import PagedBetree
  import AbstractMap
  import CrashTolerantMap

  predicate FreshLabel(v: CoordinationBetree.Variables, lbl: CoordinationBetree.TransitionLabel)
  {
    && (lbl.InternalLabel? ==>
      && lbl.allocs !! v.persistent.value.AccessibleAUs()
      && (v.ephemeral.Known? ==> lbl.allocs !! v.ephemeral.v.AccessibleAUs())
      && (v.inFlight.Some? ==> lbl.allocs !! v.inFlight.value.value.AccessibleAUs()))
  }

  predicate BetreeStatesAgrees(v: CoordinationBetree.Variables)
  {
    && ( v.ephemeral.Known? && v.inFlight.Some? ==>
      && var ephemeralBetreeDisk := v.ephemeral.v.likesVars.branchedVars.branched.diskView;
      && var ephemeralBranchDisk := v.ephemeral.v.allocBranchDiskView;
      && var inFlightBetreeDisk := v.inFlight.value.value.branched.diskView;
      && var inFlightBranchisk := v.inFlight.value.value.dv;
      && MapsAgree(ephemeralBetreeDisk.entries, inFlightBetreeDisk.entries)
      && MapsAgree(ephemeralBranchDisk.entries, inFlightBranchisk.entries))
    && ( v.ephemeral.Known? ==>
      && var ephemeralBetreeDisk := v.ephemeral.v.likesVars.branchedVars.branched.diskView;
      && var ephemeralBranchDisk := v.ephemeral.v.allocBranchDiskView;
      && var persistentBetreeDisk := v.persistent.value.branched.diskView;
      && var persistentBranchisk := v.persistent.value.dv;
      && MapsAgree(ephemeralBetreeDisk.entries, persistentBetreeDisk.entries)
      && MapsAgree(ephemeralBranchDisk.entries, persistentBranchisk.entries))
  }

  predicate InFlightAndPersistentImagesNotFree(v: CoordinationBetree.Variables)
  {
    && ( v.ephemeral.Known? && v.inFlight.Some? ==>
      && v.ephemeral.v.compactor.AUs() !! v.inFlight.value.value.AccessibleAUs())
    && ( v.ephemeral.Known? ==>
      && v.ephemeral.v.compactor.AUs() !! v.persistent.value.AccessibleAUs()) 
  }

  predicate Inv(v: CoordinationBetree.Variables)
  {
    && (v.ephemeral.Unknown? ==> v.inFlight.None?)
    && (v.ephemeral.Known? ==> AllocationBetreeRefinement.Inv(v.ephemeral.v))
    && (v.inFlight.Some? ==> AllocationBetreeRefinement.ValidStampedBetree(v.inFlight.value))
    && AllocationBetreeRefinement.ValidStampedBetree(v.persistent)

    && BetreeStatesAgrees(v)
    && InFlightAndPersistentImagesNotFree(v)
  }

  function ILbl(lbl: CoordinationBetree.TransitionLabel) : CrashTolerantMap.TransitionLabel
  {
    match lbl
      case LoadEphemeralFromPersistentLabel(endLsn) => CrashTolerantMap.LoadEphemeralFromPersistentLabel(endLsn)
      case PutRecordsLabel(records) => CrashTolerantMap.PutRecordsLabel(records)
      case QueryLabel(endLsn, key, value) => CrashTolerantMap.QueryLabel(endLsn, key, value)
      case FreezeAsLabel(_) => CrashTolerantMap.InternalLabel()
      case InternalLabel(_, _) => CrashTolerantMap.InternalLabel()
      case CommitStartLabel(newBoundaryLsn) => CrashTolerantMap.CommitStartLabel(newBoundaryLsn) 
      case CommitCompleteLabel() => CrashTolerantMap.CommitCompleteLabel()
      case CrashLabel() => CrashTolerantMap.CrashLabel()
  }

  function AllocLbl(v: CoordinationBetree.Variables, v': CoordinationBetree.Variables, lbl: CoordinationBetree.TransitionLabel) : AllocationBetreeMod.TransitionLabel
    requires CoordinationBetree.Next(v, v', lbl)
  {
    match lbl
      case PutRecordsLabel(records) => AllocationBetreeMod.PutLabel(records)
      case QueryLabel(endLsn, key, value) => AllocationBetreeMod.QueryLabel(endLsn, key, value)
      case FreezeAsLabel(unobserved) => AllocationBetreeMod.FreezeAsLabel(v'.inFlight.value, lbl.unobserved)
      case InternalLabel(allocs, deallocs) => AllocationBetreeMod.InternalAllocationsLabel(allocs, deallocs)
      case _ => AllocationBetreeMod.InternalAllocationsLabel({}, {}) // no op label
  }

  function IBetree(betree: AllocationBetreeMod.Variables) : AbstractMap.Variables
    requires AllocationBetreeRefinement.Inv(betree)
  {
    var likesBetree := AllocationBetreeRefinement.I(betree);
    var branchedBetree := LikesBetreeRefinement.I(likesBetree);
    var linkedBetree := BranchedBetreeRefinement.I(branchedBetree);
    var filteredBetree := LinkedBetreeRefinement.I(linkedBetree);
    var pivotBetree := FilteredBetreeRefinement.I(filteredBetree);
    var pagedBetree := PivotBetreeRefinement.I(pivotBetree);
    var abstractMap := PagedBetreeRefinement.I(pagedBetree);
    abstractMap
  }

  function IBetreeImage(image: AllocationBetreeMod.StampedBetree) : CrashTolerantMap.StoreImage
    requires image.value.branched.Acyclic()
  {
    var branchedImage := AllocationBetreeRefinement.IStampedBetree(image);
    var linkedImage := BranchedBetreeRefinement.IStampedBetree(branchedImage);
    var filteredImage := LinkedBetreeRefinement.IStampedBetree(linkedImage);
    var pivotImage := FilteredBetreeRefinement.IStampedBetree(filteredImage);
    var pagedImage := PivotBetreeRefinement.IStampedBetree(pivotImage);
    var mapImage := PagedBetreeRefinement.IStampedBetree(pagedImage);
    mapImage
  }

  function IEphemeral(ephemeral: CoordinationBetree.Ephemeral) : CrashTolerantMap.Ephemeral
    requires ephemeral.Known? ==> AllocationBetreeRefinement.Inv(ephemeral.v)
  {
    if ephemeral.Unknown? then CrashTolerantMap.Unknown
    else CrashTolerantMap.Known(IBetree(ephemeral.v))
  }

  function I(v: CoordinationBetree.Variables) : CrashTolerantMap.Variables
    requires Inv(v)
  {
    CrashTolerantMap.Variables(
      IBetreeImage(v.persistent), 
      IEphemeral(v.ephemeral),
      if v.inFlight.Some? then Some(IBetreeImage(v.inFlight.value)) else None
    )
  }

  lemma InternalLabelNextPreservesInv(v: CoordinationBetree.Variables, v': CoordinationBetree.Variables, lbl: CoordinationBetree.TransitionLabel)
    requires Inv(v)
    requires FreshLabel(v, lbl)
    requires lbl.InternalLabel?
    requires CoordinationBetree.Next(v, v', lbl)
    ensures Inv(v')
    {
      AllocationBetreeRefinement.NextRefines(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl));
      var allocStep :| AllocationBetreeMod.NextStep(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl), allocStep);
      match allocStep {
        case InternalGrowStep(_) => {}
        case InternalSplitStep(path, request, newAddrs, pathAddrs) => {
          assert InFlightAndPersistentImagesNotFree(v');
          assume BetreeStatesAgrees(v');
        }
        case InternalFlushMemtableStep(_,_) => {
          assert InFlightAndPersistentImagesNotFree(v');
          assume BetreeStatesAgrees(v');
        }
        case InternalFlushStep(_, _, _, _, _, _) => {
          assert InFlightAndPersistentImagesNotFree(v');
          assume BetreeStatesAgrees(v');
        }
        case InternalCompactBeginStep(path, start, end) => {        
          var compactInput := AllocationBetreeMod.GetCompactInput(path, start, end, v.ephemeral.v.allocBranchDiskView);
          var compactLbl := CompactorMod.BeginLabel(compactInput, lbl.allocs);
          CompactorMod.CompactBeginExtendsAU(v.ephemeral.v.compactor, v'.ephemeral.v.compactor, compactLbl);
        }
        case InternalCompactBuildStep() => {
          var compactLbl := CompactorMod.InternalLabel(lbl.allocs);
          CompactorMod.CompactInternalExtendsAU(v.ephemeral.v.compactor, v'.ephemeral.v.compactor, compactLbl);
        }
        case InternalCompactCommitStep(_, _, _, _, _, _) => {
          AllocationBetreeMod.InternalCompactCommitCompactorEffects(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl), allocStep);
          assert v'.ephemeral.v.compactor.AUs() <= v.ephemeral.v.compactor.AUs();
          assert InFlightAndPersistentImagesNotFree(v');
          assume BetreeStatesAgrees(v');
        }
        case InternalNoOpStep() => {}
        case _ => assert false;
    }
  }

  lemma InvNext(v: CoordinationBetree.Variables, v': CoordinationBetree.Variables, lbl: CoordinationBetree.TransitionLabel)
    requires Inv(v)
    requires FreshLabel(v, lbl)
    requires CoordinationBetree.Next(v, v', lbl)
    ensures Inv(v')
  {
    match lbl {
      case LoadEphemeralFromPersistentLabel(_) => { AllocationBetreeRefinement.InitRefines(v'.ephemeral.v, v.persistent); }
      case PutRecordsLabel(records) => {}
      case QueryLabel(endLsn, key, value) => {}
      case FreezeAsLabel(unobserved) => {}
      case InternalLabel(allocs, deallocs) => { InternalLabelNextPreservesInv(v, v', lbl); }
      case CommitStartLabel(newBoundaryLsn) => {} 
      case CommitCompleteLabel() => {}
      case CrashLabel() => {}
    } 
  }

  lemma InitRefines(v: CoordinationBetree.Variables)
    requires CoordinationBetree.Init(v)
    ensures Inv(v)
    ensures CrashTolerantMap.Init(I(v))
  {
    PagedBetreeRefinement.EmptyImageRefines();
  }

  lemma NextRefines(v: CoordinationBetree.Variables, v': CoordinationBetree.Variables, lbl: CoordinationBetree.TransitionLabel)
    requires Inv(v)
    requires FreshLabel(v, lbl)
    requires CoordinationBetree.Next(v, v', lbl)
    ensures Inv(v')
    ensures CrashTolerantMap.Next(I(v), I(v'), ILbl(lbl))
  {
    assume false;
    // match lbl {
    //   case LoadEphemeralFromPersistentLabel() => {}
    //   case ReadForRecoveryLabel(records) => { AllocNextRefinesAbstract(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl)); }
    //   case QueryEndLsnLabel(_) => {}
    //   case PutLabel(_) => { AllocNextRefinesAbstract(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl)); }
    //   case InternalLabel(allocs, deallocs) => { AllocNextRefinesAbstract(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl)); }
    //   case QueryLsnPersistenceLabel(_) => {}
    //   case FreezeAsLabel(_) => {}
    //   case CommitStartLabel(_, _) => { AllocNextRefinesAbstract(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl)); }
    //   case CommitCompleteLabel(_, _)=> { AllocNextRefinesAbstract(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl)); }
    //   case CrashLabel() => {}
    // }
  }
}
