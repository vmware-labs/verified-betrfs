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
  import opened Sequences
  import M = Mathematics
  import G = GenericDisk
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

  // split into FullStackBetreeRefinement and coordinationbetree refinement

  predicate FreshLabel(v: CoordinationBetree.Variables, lbl: CoordinationBetree.TransitionLabel)
  {
    && (lbl.InternalLabel? ==>
      && lbl.allocs !! v.persistent.value.AccessibleAUs()
      && (v.ephemeral.Known? ==> lbl.allocs !! v.ephemeral.v.AccessibleAUs())
      && (v.inFlight.Some? ==> lbl.allocs !! v.inFlight.value.value.AccessibleAUs()))
  }

  lemma FreshLabelImpliesDisjointAddrs(v: CoordinationBetree.Variables, lbl: CoordinationBetree.TransitionLabel, addrs: set<G.Address>)
    requires lbl.InternalLabel?
    requires FreshLabel(v, lbl)
    requires G.ToAUs(addrs) <= lbl.allocs
    ensures addrs !! v.persistent.value.branched.diskView.entries.Keys
    ensures addrs !! v.persistent.value.dv.entries.Keys
    ensures v.inFlight.Some? ==> addrs !! v.inFlight.value.value.branched.diskView.entries.Keys
    ensures v.inFlight.Some? ==> addrs !! v.inFlight.value.value.dv.entries.Keys
  {
    forall addr | addr in addrs 
      ensures addr !in v.persistent.value.branched.diskView.entries.Keys
      ensures addr !in v.persistent.value.dv.entries.Keys
      ensures v.inFlight.Some? ==> addr !in v.inFlight.value.value.branched.diskView.entries.Keys
      ensures v.inFlight.Some? ==> addr !in v.inFlight.value.value.dv.entries.Keys
    {
      if addr in v.persistent.value.branched.diskView.entries.Keys || addr in v.persistent.value.dv.entries.Keys {
        assert addr.au in v.persistent.value.AccessibleAUs();
        assert false;
      }

      if v.inFlight.Some? {
        if addr in v.inFlight.value.value.branched.diskView.entries.Keys || addr in v.inFlight.value.value.dv.entries.Keys {
          assert addr.au in v.inFlight.value.value.AccessibleAUs();
          assert false;
        }
      }
    }
  }

  lemma CompactorImpliesDisjointAddrs(v: CoordinationBetree.Variables, addrs: set<G.Address>)
    requires v.ephemeral.Known?
    requires G.ToAUs(addrs) <= v.ephemeral.v.compactor.AUs()
    requires InFlightAndPersistentImagesNotFree(v)
    ensures addrs !! v.persistent.value.branched.diskView.entries.Keys
    ensures addrs !! v.persistent.value.dv.entries.Keys
    ensures v.inFlight.Some? ==> addrs !! v.inFlight.value.value.branched.diskView.entries.Keys
    ensures v.inFlight.Some? ==> addrs !! v.inFlight.value.value.dv.entries.Keys
  {
    forall addr | addr in addrs 
      ensures addr !in v.persistent.value.branched.diskView.entries.Keys
      ensures addr !in v.persistent.value.dv.entries.Keys
      ensures v.inFlight.Some? ==> addr !in v.inFlight.value.value.branched.diskView.entries.Keys
      ensures v.inFlight.Some? ==> addr !in v.inFlight.value.value.dv.entries.Keys
    {
      if addr in v.persistent.value.branched.diskView.entries.Keys || addr in v.persistent.value.dv.entries.Keys {
        assert addr.au in v.persistent.value.AccessibleAUs();
        assert false;
      }

      if v.inFlight.Some? {
        if addr in v.inFlight.value.value.branched.diskView.entries.Keys || addr in v.inFlight.value.value.dv.entries.Keys {
          assert addr.au in v.inFlight.value.value.AccessibleAUs();
          assert false;
        }
      }
    }
  }

  predicate BetreeStatesAgrees(v: CoordinationBetree.Variables)
  {
    // AgreesWithDisk // todo: change text
    && ( v.ephemeral.Known? && v.inFlight.Some? ==>
      && var ephemeralBetreeDisk := v.ephemeral.v.likesVars.branchedVars.branched.diskView;
      && var ephemeralBranchDisk := v.ephemeral.v.allocBranchDiskView;
      && var inFlightBetreeDisk := v.inFlight.value.value.branched.diskView;
      && var inFlightBranchisk := v.inFlight.value.value.dv;
      && ephemeralBetreeDisk.AgreesWithDisk(inFlightBetreeDisk)
      && ephemeralBranchDisk.AgreesWithDisk(inFlightBranchisk))
    && ( v.ephemeral.Known? ==>
      && var ephemeralBetreeDisk := v.ephemeral.v.likesVars.branchedVars.branched.diskView;
      && var ephemeralBranchDisk := v.ephemeral.v.allocBranchDiskView;
      && var persistentBetreeDisk := v.persistent.value.branched.diskView;
      && var persistentBranchisk := v.persistent.value.dv;
      && ephemeralBetreeDisk.AgreesWithDisk(persistentBetreeDisk)
      && ephemeralBranchDisk.AgreesWithDisk(persistentBranchisk))
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

    // not needed for stack refinement but will be used by cache
    && BetreeStatesAgrees(v)
    && InFlightAndPersistentImagesNotFree(v)
  }

  function ILbl(lbl: CoordinationBetree.TransitionLabel) : CrashTolerantMap.TransitionLabel
  {
    match lbl
      case LoadEphemeralFromPersistentLabel(endLsn) => CrashTolerantMap.LoadEphemeralFromPersistentLabel(endLsn)
      case PutRecordsLabel(records) => CrashTolerantMap.PutRecordsLabel(records)
      case QueryLabel(endLsn, key, value) => CrashTolerantMap.QueryLabel(endLsn, key, value)
      case InternalLabel(_, _) => CrashTolerantMap.InternalLabel()
      case CommitStartLabel(newBoundaryLsn) => CrashTolerantMap.CommitStartLabel(newBoundaryLsn) 
      case CommitCompleteLabel() => CrashTolerantMap.CommitCompleteLabel()
      case CrashLabel() => CrashTolerantMap.CrashLabel()
  }

  function IAllocLbl(lbl: AllocationBetreeMod.TransitionLabel) : AbstractMap.TransitionLabel
  {
    var linkedLbl := BranchedBetreeRefinement.ILbl(lbl.I().I());
    var filteredLbl := LinkedBetreeRefinement.ILbl(linkedLbl);
    var pivotLbl := FilteredBetreeRefinement.ILbl(filteredLbl);
    var pagedLbl := PivotBetreeRefinement.ILbl(pivotLbl);
    var mapLbl := PagedBetreeRefinement.ILbl(pagedLbl);
    mapLbl
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

  lemma AllocInternalSplitStepPreservesInv(v: CoordinationBetree.Variables, v': CoordinationBetree.Variables, lbl: CoordinationBetree.TransitionLabel, allocStep: AllocationBetreeMod.Step)
    requires Inv(v)
    requires FreshLabel(v, lbl)
    requires CoordinationBetree.EphemeralInternal(v, v', lbl)
    requires allocStep.InternalSplitStep?
    requires AllocationBetreeMod.NextStep(v.ephemeral.v, v'.ephemeral.v, 
      AllocationBetreeMod.InternalAllocationsLabel(lbl.allocs, lbl.deallocs), allocStep)
    requires AllocationBetreeRefinement.Inv(v'.ephemeral.v)
    ensures Inv(v')
  {
    var pathAddrs := allocStep.pathAddrs;
    var newAddrs := allocStep.newAddrs;
    var ephemeralBetreeDisk := v.ephemeral.v.likesVars.branchedVars.branched.diskView;
    var ephemeralBetreeDisk' := v'.ephemeral.v.likesVars.branchedVars.branched.diskView;
    var betreeNewAddrs := Set(pathAddrs) + newAddrs.Repr();

    assume MapsAgree(ephemeralBetreeDisk.entries, ephemeralBetreeDisk'.entries);
    assume ephemeralBetreeDisk'.entries.Keys - ephemeralBetreeDisk.entries.Keys == betreeNewAddrs;

    FreshLabelImpliesDisjointAddrs(v, lbl, betreeNewAddrs);
    assert BetreeStatesAgrees(v');
    assert InFlightAndPersistentImagesNotFree(v');
  }

  lemma AllocInternalFlushMemtableStepPreservesInv(v: CoordinationBetree.Variables, v': CoordinationBetree.Variables, lbl: CoordinationBetree.TransitionLabel, allocStep: AllocationBetreeMod.Step)
    requires Inv(v)
    requires FreshLabel(v, lbl)
    requires CoordinationBetree.EphemeralInternal(v, v', lbl)
    requires allocStep.InternalFlushMemtableStep?
    requires AllocationBetreeMod.NextStep(v.ephemeral.v, v'.ephemeral.v, 
      AllocationBetreeMod.InternalAllocationsLabel(lbl.allocs, lbl.deallocs), allocStep)
    requires AllocationBetreeRefinement.Inv(v'.ephemeral.v)
    ensures Inv(v')
  {
    var newRootAddr := allocStep.newRootAddr;
    var branch := allocStep.branch;
    var ephemeralBetreeDisk := v.ephemeral.v.likesVars.branchedVars.branched.diskView;
    var ephemeralBetreeDisk' := v'.ephemeral.v.likesVars.branchedVars.branched.diskView;    
    var betreeNewAddrs := {newRootAddr};

    assume MapsAgree(ephemeralBetreeDisk.entries, ephemeralBetreeDisk'.entries);
    assume ephemeralBetreeDisk'.entries.Keys - ephemeralBetreeDisk.entries.Keys == betreeNewAddrs;

    var branchNewAddrs := branch.Representation();
    var ephemeralBranchDisk := v.ephemeral.v.allocBranchDiskView;
    var ephemeralBranchDisk' := v'.ephemeral.v.allocBranchDiskView;
          
    assume MapsAgree(ephemeralBranchDisk.entries, ephemeralBranchDisk'.entries);
    assume ephemeralBranchDisk'.entries.Keys - ephemeralBranchDisk.entries.Keys == branchNewAddrs;
    assume G.ToAUs(branchNewAddrs) == branch.GetSummary(); // maintained as part of allocationbetree inv

    FreshLabelImpliesDisjointAddrs(v, lbl, betreeNewAddrs);
    FreshLabelImpliesDisjointAddrs(v, lbl, branchNewAddrs);

    assert BetreeStatesAgrees(v');
    assert InFlightAndPersistentImagesNotFree(v');
  }

  lemma AllocInternalFlushStepPreservesInv(v: CoordinationBetree.Variables, v': CoordinationBetree.Variables, lbl: CoordinationBetree.TransitionLabel, allocStep: AllocationBetreeMod.Step)
    requires Inv(v)
    requires FreshLabel(v, lbl)
    requires CoordinationBetree.EphemeralInternal(v, v', lbl)
    requires allocStep.InternalFlushStep?
    requires AllocationBetreeMod.NextStep(v.ephemeral.v, v'.ephemeral.v, 
      AllocationBetreeMod.InternalAllocationsLabel(lbl.allocs, lbl.deallocs), allocStep)
    requires AllocationBetreeRefinement.Inv(v'.ephemeral.v)
    ensures Inv(v')
  {  
    var ephemeralBetreeDisk := v.ephemeral.v.likesVars.branchedVars.branched.diskView;
    var ephemeralBetreeDisk' := v'.ephemeral.v.likesVars.branchedVars.branched.diskView;   
    var betreeNewAddrs := {allocStep.targetAddr} + {allocStep.targetChildAddr} + Set(allocStep.pathAddrs);

    assume MapsAgree(ephemeralBetreeDisk.entries, ephemeralBetreeDisk'.entries);
    assume ephemeralBetreeDisk'.entries.Keys - ephemeralBetreeDisk.entries.Keys == betreeNewAddrs;
    FreshLabelImpliesDisjointAddrs(v, lbl, betreeNewAddrs);

    var ephemeralBranchDisk := v.ephemeral.v.allocBranchDiskView;
    var ephemeralBranchDisk' := v'.ephemeral.v.allocBranchDiskView;
    assert ephemeralBranchDisk'.IsSubsetOf(ephemeralBranchDisk);

    assert BetreeStatesAgrees(v');
    assert InFlightAndPersistentImagesNotFree(v');
  }

  lemma AllocInternalCompactCommitStepPreservesInv(v: CoordinationBetree.Variables, v': CoordinationBetree.Variables, lbl: CoordinationBetree.TransitionLabel, allocStep: AllocationBetreeMod.Step)
    requires Inv(v)
    requires FreshLabel(v, lbl)
    requires CoordinationBetree.EphemeralInternal(v, v', lbl)
    requires allocStep.InternalCompactCommitStep?
    requires AllocationBetreeMod.NextStep(v.ephemeral.v, v'.ephemeral.v, 
      AllocationBetreeMod.InternalAllocationsLabel(lbl.allocs, lbl.deallocs), allocStep)
    requires AllocationBetreeRefinement.Inv(v'.ephemeral.v)
    ensures Inv(v')
  {
    assert v'.inFlight == v.inFlight;
    assert v'.persistent == v.persistent;

    AllocationBetreeMod.InternalCompactCommitCompactorEffects(v.ephemeral.v, v'.ephemeral.v, 
      AllocationBetreeMod.InternalAllocationsLabel(lbl.allocs, lbl.deallocs), allocStep);
    assert allocStep.newBranch.WF();
    assert v'.ephemeral.v.compactor.AUs() + allocStep.newBranch.GetSummary() == v.ephemeral.v.compactor.AUs();
    assert allocStep.newBranch.GetSummary() <= v.ephemeral.v.compactor.AUs();
    assert InFlightAndPersistentImagesNotFree(v');

    var ephemeralBetreeDisk := v.ephemeral.v.likesVars.branchedVars.branched.diskView;
    var ephemeralBetreeDisk' := v'.ephemeral.v.likesVars.branchedVars.branched.diskView;    
    var betreeNewAddrs := Set(allocStep.pathAddrs) + {allocStep.targetAddr};

    assume MapsAgree(ephemeralBetreeDisk.entries, ephemeralBetreeDisk'.entries);
    assume ephemeralBetreeDisk'.entries.Keys - ephemeralBetreeDisk.entries.Keys == betreeNewAddrs;
    FreshLabelImpliesDisjointAddrs(v, lbl, betreeNewAddrs);

    var ephemeralBranchDisk := v.ephemeral.v.allocBranchDiskView;
    var ephemeralBranchDisk' := v'.ephemeral.v.allocBranchDiskView;
    var branchNewAddrs := allocStep.newBranch.diskView.entries.Keys;

    assume MapsAgree(ephemeralBranchDisk.entries, ephemeralBranchDisk'.entries);
    assume ephemeralBranchDisk'.entries.Keys - ephemeralBranchDisk.entries.Keys == branchNewAddrs;
    assume G.ToAUs(branchNewAddrs) == allocStep.newBranch.GetSummary();

    CompactorImpliesDisjointAddrs(v, branchNewAddrs);
  }

  lemma EphemeralInternalStepPreservesInv(v: CoordinationBetree.Variables, v': CoordinationBetree.Variables, lbl: CoordinationBetree.TransitionLabel)
    requires Inv(v)
    requires FreshLabel(v, lbl)
    requires CoordinationBetree.EphemeralInternal(v, v', lbl)
    ensures Inv(v')
    {
      var allocLbl := AllocationBetreeMod.InternalAllocationsLabel(lbl.allocs, lbl.deallocs);
      AllocationBetreeRefinement.NextRefines(v.ephemeral.v, v'.ephemeral.v, allocLbl);

      var allocStep :| AllocationBetreeMod.NextStep(v.ephemeral.v, v'.ephemeral.v, allocLbl, allocStep);
      match allocStep {
        case InternalGrowStep(_) => {}
        case InternalSplitStep(_, _, _, _) => AllocInternalSplitStepPreservesInv(v, v', lbl, allocStep);
        case InternalFlushMemtableStep(_, _) => AllocInternalFlushMemtableStepPreservesInv(v, v', lbl, allocStep);
        case InternalFlushStep(_, _, _, _, _, _) => AllocInternalFlushStepPreservesInv(v, v', lbl, allocStep);
        case InternalCompactBeginStep(path, start, end) => 
        {
          var compactInput := AllocationBetreeMod.GetCompactInput(path, start, end, v.ephemeral.v.allocBranchDiskView);
          var compactLbl := CompactorMod.BeginLabel(compactInput, lbl.allocs);
          CompactorMod.CompactBeginExtendsAU(v.ephemeral.v.compactor, v'.ephemeral.v.compactor, compactLbl);
        }
        case InternalCompactBuildStep() =>
        {
          var compactLbl := CompactorMod.InternalLabel(lbl.allocs);
          CompactorMod.CompactInternalExtendsAU(v.ephemeral.v.compactor, v'.ephemeral.v.compactor, compactLbl);
        }
        case InternalCompactCommitStep(_, _, _, _, _, _) => AllocInternalCompactCommitStepPreservesInv(v, v', lbl, allocStep);
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
    var step :| CoordinationBetree.NextStep(v, v', lbl, step);
    match step {
      case LoadEphemeralFromPersistentStep() => AllocationBetreeRefinement.InitRefines(v'.ephemeral.v, v.persistent);
      case PutRecordsStep() => {}
      case QueryStep() => {}
      case FreezeBetreeInternalStep(frozenBetree) => { 
        var allocLbl := AllocationBetreeMod.FreezeAsLabel(frozenBetree);
        AllocationBetreeRefinement.NextRefines(v.ephemeral.v, v'.ephemeral.v, allocLbl);        
      }
      case FreezeFromPersistentInternalStep() => {}
      case EphemeralInternalStep() => EphemeralInternalStepPreservesInv(v, v', lbl);
      case CommitStartStep() => {}
      case CommitCompleteStep() => {}
      case CrashStep() => {}
    }
  }

  lemma InitRefines(v: CoordinationBetree.Variables)
    requires CoordinationBetree.Init(v)
    ensures Inv(v)
    ensures CrashTolerantMap.Init(I(v))
  {
    PagedBetreeRefinement.EmptyImageRefines();
  }

  lemma AllocInitRefinesAbstract(v: AllocationBetreeMod.Variables, image: AllocationBetreeMod.StampedBetree)
    requires AllocationBetreeRefinement.Inv(v)
    requires AllocationBetreeMod.Init(v, image)
    ensures AbstractMap.Init(IBetree(v), IBetreeImage(image))
  {
    AllocationBetreeRefinement.InitRefines(v, image);
    
    var likesBetree := AllocationBetreeRefinement.I(v);
    var likesImage := AllocationBetreeRefinement.IStampedBetree(image);
    LikesBetreeRefinement.InitRefines(likesBetree, likesImage);

    var branchedBetree := LikesBetreeRefinement.I(likesBetree);
    var branchedImage := LikesBetreeRefinement.IStampedBetree(likesImage);
    BranchedBetreeRefinement.InitRefines(branchedBetree, branchedImage);

    var linkedBetree := BranchedBetreeRefinement.I(branchedBetree);
    var linkedImage := BranchedBetreeRefinement.IStampedBetree(branchedImage);
    LinkedBetreeRefinement.InitRefines(linkedBetree, linkedImage);

    var filteredBetree := LinkedBetreeRefinement.I(linkedBetree);
    var filteredImage := LinkedBetreeRefinement.IStampedBetree(linkedImage);
    FilteredBetreeRefinement.InitRefines(filteredBetree, filteredImage);

    var pivotBetree := FilteredBetreeRefinement.I(filteredBetree);
    var pivotImage := FilteredBetreeRefinement.IStampedBetree(filteredImage);
    PivotBetreeRefinement.InitRefines(pivotBetree, pivotImage);

    var pagedBetree := PivotBetreeRefinement.I(pivotBetree);
    var pagedImage := PivotBetreeRefinement.IStampedBetree(pivotImage);
    PagedBetreeRefinement.InitRefines(pagedBetree, pagedImage);
  }

  lemma AllocNextRefinesAbstract(v: AllocationBetreeMod.Variables, v': AllocationBetreeMod.Variables, lbl: AllocationBetreeMod.TransitionLabel)
    requires AllocationBetreeRefinement.Inv(v)
    requires AllocationBetreeRefinement.Inv(v')
    requires AllocationBetreeMod.Next(v, v', lbl)
    requires AllocationBetreeRefinement.FreshLabel(v, lbl)
    ensures AbstractMap.Next(IBetree(v), IBetree(v'), IAllocLbl(lbl))
  {
    AllocationBetreeRefinement.NextRefines(v, v', lbl);
    
    var likesBetree := AllocationBetreeRefinement.I(v);
    var likesBetree' := AllocationBetreeRefinement.I(v');
    LikesBetreeRefinement.NextRefines(likesBetree, likesBetree', lbl.I());

    var branchedBetree := LikesBetreeRefinement.I(likesBetree);
    var branchedBetree' := LikesBetreeRefinement.I(likesBetree');
    BranchedBetreeRefinement.NextRefines(branchedBetree, branchedBetree', lbl.I().I());

    var linkedBetree := BranchedBetreeRefinement.I(branchedBetree);
    var linkedBetree' := BranchedBetreeRefinement.I(branchedBetree');
    var linkedLbl := BranchedBetreeRefinement.ILbl(lbl.I().I());
    LinkedBetreeRefinement.NextRefines(linkedBetree, linkedBetree', linkedLbl);

    var filteredBetree := LinkedBetreeRefinement.I(linkedBetree);
    var filteredBetree' := LinkedBetreeRefinement.I(linkedBetree');
    var filteredLbl := LinkedBetreeRefinement.ILbl(linkedLbl);
    FilteredBetreeRefinement.NextRefines(filteredBetree, filteredBetree', filteredLbl);

    var pivotBetree := FilteredBetreeRefinement.I(filteredBetree);
    var pivotBetree' := FilteredBetreeRefinement.I(filteredBetree');
    var pivotLbl := FilteredBetreeRefinement.ILbl(filteredLbl);
    PivotBetreeRefinement.NextRefines(pivotBetree, pivotBetree', pivotLbl);

    var pagedBetree := PivotBetreeRefinement.I(pivotBetree);
    var pagedBetree' := PivotBetreeRefinement.I(pivotBetree');
    var pagedLbl := PivotBetreeRefinement.ILbl(pivotLbl);
    PagedBetreeRefinement.NextRefines(pagedBetree, pagedBetree', pagedLbl);
  }

  lemma NextRefines(v: CoordinationBetree.Variables, v': CoordinationBetree.Variables, lbl: CoordinationBetree.TransitionLabel)
    requires Inv(v)
    requires FreshLabel(v, lbl)
    requires CoordinationBetree.Next(v, v', lbl)
    ensures Inv(v')
    ensures CrashTolerantMap.Next(I(v), I(v'), ILbl(lbl))
  {
    InvNext(v, v', lbl);

    var step :| CoordinationBetree.NextStep(v, v', lbl, step);
    match step {
      case LoadEphemeralFromPersistentStep() => {
        AllocInitRefinesAbstract(v'.ephemeral.v, v.persistent);
        assert CrashTolerantMap.NextStep(I(v), I(v'), ILbl(lbl), CrashTolerantMap.LoadEphemeralFromPersistentStep());
      }
      case PutRecordsStep() => {
        var allocLbl := AllocationBetreeMod.PutLabel(lbl.records);
        AllocNextRefinesAbstract(v.ephemeral.v, v'.ephemeral.v, allocLbl);
        assert CrashTolerantMap.NextStep(I(v), I(v'), ILbl(lbl), CrashTolerantMap.PutRecordsStep());
      }
      case QueryStep() => {
        var allocLbl := AllocationBetreeMod.QueryLabel(lbl.endLsn, lbl.key, lbl.value);
        AllocNextRefinesAbstract(v.ephemeral.v, v'.ephemeral.v, allocLbl);
        assert CrashTolerantMap.NextStep(I(v), I(v'), ILbl(lbl), CrashTolerantMap.QueryStep());
      }
      case FreezeBetreeInternalStep(frozenBetree) => {
        var frozenMap := IBetreeImage(frozenBetree);
        var allocLbl := AllocationBetreeMod.FreezeAsLabel(frozenBetree);
        AllocNextRefinesAbstract(v.ephemeral.v, v'.ephemeral.v, allocLbl);
        assert CrashTolerantMap.NextStep(I(v), I(v'), ILbl(lbl), CrashTolerantMap.FreezeMapInternalStep(frozenMap));
      }
      case FreezeFromPersistentInternalStep() => {
        assert CrashTolerantMap.NextStep(I(v), I(v'), ILbl(lbl), CrashTolerantMap.FreezeFromPersistentInternalStep());
      }
      case EphemeralInternalStep() => {
        var allocLbl := AllocationBetreeMod.InternalAllocationsLabel(lbl.allocs, lbl.deallocs);
        AllocNextRefinesAbstract(v.ephemeral.v, v'.ephemeral.v, allocLbl);
        assert CrashTolerantMap.NextStep(I(v), I(v'), ILbl(lbl), CrashTolerantMap.EphemeralInternalStep());
      }
      case CommitStartStep() => {
        assert CrashTolerantMap.NextStep(I(v), I(v'), ILbl(lbl), CrashTolerantMap.CommitStartStep());
      }
      case CommitCompleteStep() => {
        assert CrashTolerantMap.NextStep(I(v), I(v'), ILbl(lbl), CrashTolerantMap.CommitCompleteStep());
      }
      case CrashStep() => {
        assert CrashTolerantMap.NextStep(I(v), I(v'), ILbl(lbl), CrashTolerantMap.CrashStep());
      }
    }
  }

  lemma InternalLabelAccessibleAUs(v: CoordinationBetree.Variables, v': CoordinationBetree.Variables, lbl: CoordinationBetree.TransitionLabel)
    requires Inv(v)
    requires FreshLabel(v, lbl)
    requires lbl.InternalLabel?
    requires lbl.allocs !! lbl.deallocs
    requires CoordinationBetree.Next(v, v', lbl)
    requires Inv(v')
    ensures v.EphemeralAUs() + lbl.allocs - lbl.deallocs == v'.EphemeralAUs()
  {
    var step :| CoordinationBetree.NextStep(v, v', lbl, step);
    if step.EphemeralInternalStep? {
      var allocLbl := AllocationBetreeMod.InternalAllocationsLabel(lbl.allocs, lbl.deallocs);
      var allocStep :| AllocationBetreeMod.NextStep(v.ephemeral.v, v'.ephemeral.v, allocLbl, allocStep);
      assume false;
    } else {
      assert step.FreezeBetreeInternalStep? || step.FreezeFromPersistentInternalStep?;
      assert v.EphemeralAUs() == v'.EphemeralAUs();
    }
  }

  lemma FreezeBetreeInternalLemma(v: CoordinationBetree.Variables, v': CoordinationBetree.Variables, lbl: CoordinationBetree.TransitionLabel, step: CoordinationBetree.Step)
    requires Inv(v)
    requires FreshLabel(v, lbl)
    requires step.FreezeBetreeInternalStep?
    requires CoordinationBetree.FreezeBetreeInternal(v, v', lbl, step.frozenBetree)
    requires Inv(v')
    ensures v.EphemeralAUs() == v'.EphemeralAUs()
    ensures v'.InFlightAUs() <= v.EphemeralAUs()
  {
    assert v.ephemeral == v'.ephemeral;
    assert step.frozenBetree.value.branched == v.ephemeral.v.likesVars.branchedVars.branched;
    assume v.ephemeral.v.likesVars.branchedVars.branched.diskView.entries.Keys == M.Set(v.ephemeral.v.likesVars.betreeLikes); // by likesbetree Inv
    assume G.ToAUs(M.Set(v.ephemeral.v.likesVars.betreeLikes)) == M.Set(v.ephemeral.v.betreeAULikes); // by allocbetree Inv
  }

  lemma LoadEphemeralFromPersistentAUs(v: CoordinationBetree.Variables, v': CoordinationBetree.Variables, lbl: CoordinationBetree.TransitionLabel)
    requires Inv(v)
    requires lbl.LoadEphemeralFromPersistentLabel?
    requires CoordinationBetree.Next(v, v', lbl)
    ensures v.PersistentAUs() == v'.EphemeralAUs()
  {
    assert v.persistent.value.branched == v'.ephemeral.v.likesVars.branchedVars.branched;
    assume v'.ephemeral.v.likesVars.branchedVars.branched.diskView.entries.Keys == M.Set(v'.ephemeral.v.likesVars.betreeLikes); // by likesbetree Inv
    assume G.ToAUs(M.Set(v'.ephemeral.v.likesVars.betreeLikes)) == M.Set(v'.ephemeral.v.betreeAULikes); // by allocbetree Inv
    assert v.persistent.value.dv == v'.ephemeral.v.allocBranchDiskView;
  }
}
