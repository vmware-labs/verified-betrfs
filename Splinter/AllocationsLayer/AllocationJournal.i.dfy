// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "MiniAllocator.i.dfy"
include "../Journal/LikesJournal.i.dfy"
include "../Likes.i.dfy"

// A Journal that keeps an in-memory index that maps each in-use LSN to the Address that stores it.
// The impl will keep such an index so that Discard can return freed Addresses without having to
// fault in the freed section of the journal to learn the chain of addresses involved.
module AllocationJournal {
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import opened Maps
  import LinkedJournal
  import LikesJournal
  import GenericDisk
  import Mathematics
  import opened LikesMod
  import opened MiniAllocatorMod

  type Pointer = GenericDisk.Pointer
  type Address = GenericDisk.Address
  type AU = GenericDisk.AU

  type DiskView = LikesJournal.DiskView
  type TruncatedJournal = LikesJournal.TruncatedJournal

  datatype JournalImage = JournalImage(
    tj: TruncatedJournal,
    first: AU
  ) {
    predicate WF()
    {
      tj.WF()
    }

    function AccessibleAUs() : set<AU>
    {
      GenericDisk.ToAUs(tj.diskView.entries.Keys)
    }
  }

  function EmptyJournalImage() : JournalImage
  {
    JournalImage(LinkedJournal.Mkfs(), 0) // arbitrary first AU
  }

  /***************************************************************************************
  *                                    Labels and defs                                   *
  ***************************************************************************************/

  datatype TransitionLabel =
      ReadForRecoveryLabel(messages: MsgHistory)
    | FreezeForCommitLabel(frozenJournal: JournalImage)
    | QueryEndLsnLabel(endLsn: LSN)
    | PutLabel(messages: MsgHistory)
    | DiscardOldLabel(startLsn: LSN, requireEnd: LSN, deallocs: set<AU>)
    // Internal-x labels refine to no-ops at the abstract spec
    // | InternalLabel()  // Local No-op label 
    | InternalAllocationsLabel(allocs: set<AU>, deallocs: set<AU>)
  {
    predicate WF() {
      && (FreezeForCommitLabel? ==> frozenJournal.tj.Decodable())
    }

    function I(): LikesJournal.TransitionLabel {
      match this {
        case ReadForRecoveryLabel(messages) => LikesJournal.ReadForRecoveryLabel(messages)
        case FreezeForCommitLabel(frozenJournal) => LikesJournal.FreezeForCommitLabel(frozenJournal.tj)
        case QueryEndLsnLabel(endLsn) => LikesJournal.QueryEndLsnLabel(endLsn)
        case PutLabel(messages) => LikesJournal.PutLabel(messages)
        case DiscardOldLabel(startLsn, requireEnd, _) => LikesJournal.DiscardOldLabel(startLsn, requireEnd)
        case InternalAllocationsLabel(allocs, deallocs) => LikesJournal.InternalLabel()
        // case InternalLabel() => LikesJournal.InternalLabel()
      }
    }
  }

  /***************************************************************************************
  *                                    State Machine                                     *
  ***************************************************************************************/

  datatype Variables = Variables(
    journal: LikesJournal.Variables,
    lsnAUIndex: map<LSN, AU>, // lsnAUAddrIndex maps in-repr lsn's to their AU addr
    first: AU, // AU of the first journal record, boundarylsn can be found in this AU
    miniAllocator: MiniAllocator
  )
  {
    predicate WF() {
      && journal.WF()
      && miniAllocator.WF()
    }

    function AccessibleAUs() : set<AU>
    {
      lsnAUIndex.Values + miniAllocator.allocs.Keys
    }
  }

  // group a couple definitions together
  predicate OnlyAdvanceLikesJournal(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && (lbl.ReadForRecoveryLabel? || lbl.QueryEndLsnLabel? || lbl.PutLabel?)
    && LikesJournal.NextStep(v.journal, v'.journal, lbl.I(), step.I())
    && v' == v.(
      journal := v'.journal
    )
  }

  // should == G.ToAUs(frozenjournal.tj.diskview.keys)
  // function frozenAUs(frozenJournal: JournalImage, lsnAUIndex: map<LSN, AU>) : (out: set<AU>)
  //   requires frozenJournal.WF()
  // {
  //   var frozenLSNs := set lsn | frozenJournal.tj.SeqStart() <= lsn < frozenJournal.tj.SeqEnd();
  //   MapRestrict(lsnAUIndex, frozenLSNs).Values
  // }

  predicate FreezeForCommit(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && lbl.FreezeForCommitLabel?
    && step.FreezeForCommitStep?

    && LikesJournal.FreezeForCommit(v.journal, v'.journal, lbl.I(), step.depth)

    && v' == v.(
      journal := v'.journal
    )
  }

  predicate InternalMiniAllocatorFill(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.InternalAllocationsLabel?
    && lbl.deallocs == {}
    && lbl.allocs !! v.miniAllocator.allocs.Keys // TODO: maybe we want to eliminate this check and just use the label
    && v' == v.(
      miniAllocator := v.miniAllocator.AddAUs(lbl.allocs)
    )
  }

  predicate InternalMiniAllocatorPrune(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.WF()
    && lbl.InternalAllocationsLabel?
    && lbl.allocs == {}
    && (forall au | au in lbl.deallocs :: v.miniAllocator.CanRemove(au))
    && v' == v.(
      miniAllocator := v.miniAllocator.Prune(lbl.deallocs)
    )
  }

  // Update lsnAUIndex with by discarding lsn's strictly smaller than bdy
  function {:opaque} lsnAUIndexDiscardUpTo(lsnAUIndex: map<LSN, AU>, bdy: LSN) : (out: map<LSN, AU>)
    ensures IsSubMap(out, lsnAUIndex)
    ensures forall k | k in out :: bdy <= k
    ensures forall k | k in lsnAUIndex &&  bdy <= k :: k in out
  {
    map x: LSN | x in lsnAUIndex && bdy <= x :: lsnAUIndex[x]
  }

  function GetFirstAU(lsnAUIndex: map<LSN, AU>, newFirst: LSN) : AU
  {
    if newFirst in lsnAUIndex 
    then lsnAUIndex[newFirst] // actual definition
    else var arbitrary :| true; arbitrary // not reachable due to invariant
  }

  predicate DiscardOld(v: Variables, v': Variables, lbl: TransitionLabel) 
  {
    && v.WF()
    // Enabling conditions
    && lbl.DiscardOldLabel?
    && LikesJournal.DiscardOld(v.journal, v'.journal, lbl.I()) 

    && var newlsnAUIndex := lsnAUIndexDiscardUpTo(v.lsnAUIndex, lbl.startLsn);
    && var discardedAUs := v.lsnAUIndex.Values - newlsnAUIndex.Values;
    && var newFirst := if v'.journal.journal.truncatedJournal.freshestRec.None? 
          then v.first else GetFirstAU(v.lsnAUIndex, lbl.startLsn); // then case garbage value
    && lbl.deallocs == discardedAUs

    && v' == v.(
      journal := v'.journal,
      lsnAUIndex := newlsnAUIndex,
      first := newFirst,
      miniAllocator := v.miniAllocator.Prune(discardedAUs * v.miniAllocator.allocs.Keys)
      // note that these AUs refine to free (in the frozen freeset) 
    )
  }

  function SingletonIndex(start: LSN, end: LSN, value: AU) : (index: map<LSN, AU>)
  {
    // Redundant domain predicate to provide both a trigger and a finite-set heuristic.
    map x: LSN | /*InRange(start, end, x) &&*/ start <= x < end :: value
  }

  // Update lsnAUIndex with additional lsn's from a new record
  function lsnAUIndexAppendRecord(lsnAUIndex: map<LSN, AU>, msgs: MsgHistory, au: AU) : (out: map<LSN, AU>)
    requires msgs.WF()
    requires msgs.seqStart < msgs.seqEnd
    ensures LikesJournal.LsnDisjoint(lsnAUIndex.Keys, msgs) ==> out.Values == lsnAUIndex.Values + {au}
  {
    // msgs is complete map from seqStart to seqEnd 
    // comprehension condition is redundant: Contains gives a trigger, <= < gives finite heuristic.
    var update := SingletonIndex(msgs.seqStart, msgs.seqEnd, au);
    var out := MapUnion(lsnAUIndex, update);
    assert LikesJournal.LsnDisjoint(lsnAUIndex.Keys, msgs)
            ==> out.Values == lsnAUIndex.Values + {au} by {
      // TODO: this be broken in likesjournal too
    }
    out
  }

  predicate ValidNextJournalAddr(v: Variables, addr: Address)
  {
    && v.miniAllocator.CanAllocate(addr)
    && (v.miniAllocator.curr.None? ==> 
      && v.miniAllocator.allocs[addr.au].AllPagesFree()
      && addr.page == 0)
    && (v.miniAllocator.curr.Some? && v.journal.journal.truncatedJournal.freshestRec.Some?
      ==> addr == v.journal.journal.truncatedJournal.freshestRec.value.NextPage())
  }

  predicate InternalJournalMarshal(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    // Enabling conditions
    && v.WF()
    && lbl == InternalAllocationsLabel({}, {})
    && step.InternalJournalMarshalStep?
    // state transition
    // constraint on what can be allocated
    && ValidNextJournalAddr(v, step.addr)
    && LinkedJournal.InternalJournalMarshalRecord(v.journal.journal, v'.journal.journal, lbl.I().I(), step.cut, step.addr)
    && var discardmsgs := v.journal.journal.unmarshalledTail.DiscardRecent(step.cut);
    && var newFirst := if v.journal.journal.truncatedJournal.freshestRec.Some? then v.first else step.addr.au;
    && v' == v.(
      journal := v'.journal.(
        journal := v'.journal.journal, // predicate updated above
        lsnAddrIndex := LikesJournal.lsnAddrIndexAppendRecord(
          v.journal.lsnAddrIndex, discardmsgs, step.addr)),
      lsnAUIndex := lsnAUIndexAppendRecord(v.lsnAUIndex, discardmsgs, step.addr.au),
      first := newFirst,
      miniAllocator := v.miniAllocator.AllocateAndObserve(step.addr)
    )
  }

  predicate InternalNoOp(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl == InternalAllocationsLabel({}, {})
    && v' == v
  }
 
  // build LSN index by walking every page
  function BuildLsnAUIndexPageWalk(dv: DiskView, root: Pointer) : map<LSN, AU> 
    requires dv.Decodable(root)
    requires dv.Acyclic()
    // requires root.Some? ==> dv.boundaryLSN < dv.entries[root.value].messageSeq.seqEnd
    decreases dv.TheRankOf(root)
  {
    if root.None? then map[]
    else 
      var currMsgs := dv.entries[root.value].messageSeq;
      var update := SingletonIndex(
        Mathematics.max(dv.boundaryLSN, currMsgs.seqStart), currMsgs.seqEnd, root.value.au);
      MapUnion(BuildLsnAUIndexPageWalk(dv, dv.entries[root.value].CroppedPrior(dv.boundaryLSN)), update)
  }

  // inv to prove transitive ranking
  // Every page in addr.au that is before addr (except page 0) is present 
  // in the diskview and points to the one before it.
  predicate AUPagesLinkedTillFirstInOrder(dv: DiskView, addr: Address)
  {
    // NOTE: just putting down a strictly decreasing order of page links
    && (forall page:nat | 0 <= page < addr.page ::
      && var priorAddr := GenericDisk.Address(addr.au, page);
      && dv.Decodable(Some(priorAddr.NextPage()))
      && dv.entries[priorAddr.NextPage()].CroppedPrior(dv.boundaryLSN) == Some(priorAddr))
  }

  // store first AU in superblock and invariant that explains this, invariant info
  lemma TransitiveRanking(dv: DiskView, root: Address, later: Address, first: AU)
    requires dv.Decodable(Some(later))
    requires dv.Acyclic()
    requires root.au != first
    requires root.au == later.au
    requires root.page <= later.page
    requires InternalAUPagesFullyLinked(dv, first)
    ensures dv.Decodable(Some(root))
    // should be less than <= bc it's enough to prove termination, cause later is already < caller's root
    ensures dv.TheRankOf(Some(root)) <= dv.TheRankOf(Some(later))
    decreases later.page
  {
    if root == later { return; }
    var prior := dv.entries[later].CroppedPrior(dv.boundaryLSN);
    var priorAddr := GenericDisk.Address(later.au, later.page-1);
    assert priorAddr.NextPage() == later;
    assert Some(priorAddr) == prior;

    TransitiveRanking(dv, root, prior.value, first);
  }

  // root should be the first page of an AU, last is the last lsn in that AU
  // first is the AU of the first journal record
  function BuildLsnAUIndexAUWalk(dv: DiskView, root: Address, last: LSN, first: AU) : map<LSN, AU>
    requires dv.Decodable(Some(root))
    requires dv.Acyclic()
    requires root.au != first
    requires root.page == 0
    requires InternalAUPagesFullyLinked(dv, first)
    decreases dv.TheRankOf(Some(root))
  {
    // we jump to the first page of each AU and perform an AU walk skipping over pages in the middle 
      var currMsgs := dv.entries[root].messageSeq;
      var update := SingletonIndex(
        Mathematics.max(dv.boundaryLSN, currMsgs.seqStart), last, root.au);

      var prior := dv.entries[root].CroppedPrior(dv.boundaryLSN);
      var priorResult := 
        if prior.None? then map[] else
          if prior.value.au == first then BuildLsnAUIndexPageWalk(dv, prior)
          else (TransitiveRanking(dv, prior.value.FirstPage(), prior.value, first);
            BuildLsnAUIndexAUWalk(dv, prior.value.FirstPage(), currMsgs.seqStart, first));

      MapUnion(priorResult, update)
  }

  function BuildLsnAUIndex(tj: TruncatedJournal, first: AU) : map<LSN, AU> 
    requires tj.Decodable()
    requires InternalAUPagesFullyLinked(tj.diskView, first)
  {
    if tj.freshestRec.None? then map[]
    else
      // if we are looking at address from the first AU, just walk the pages
      if tj.freshestRec.value.au == first then BuildLsnAUIndexPageWalk(tj.diskView, tj.freshestRec)
      else
        var last := tj.diskView.entries[tj.freshestRec.value].messageSeq.seqEnd;
        TransitiveRanking(tj.diskView, tj.freshestRec.value.FirstPage(), tj.freshestRec.value, first);
        BuildLsnAUIndexAUWalk(tj.diskView, tj.freshestRec.value.FirstPage(), last, first)
  }

  predicate InternalAUPagesFullyLinked(dv: DiskView, first: AU)
  {
    && (forall addr | addr in dv.entries && addr.au != first :: AUPagesLinkedTillFirstInOrder(dv, addr))
  }

  predicate WFAddrs(dv: DiskView)
  {
    && (forall addr | addr in dv.entries :: addr.WF())
  }

  predicate ValidJournalImage(image: JournalImage) 
  {
    && WFAddrs(image.tj.diskView)
    && InternalAUPagesFullyLinked(image.tj.diskView, image.first)
  }

  predicate Init(v: Variables, image: JournalImage)
  {
    && ValidJournalImage(image)
    && LikesJournal.Init(v.journal, image.tj)
    && v == Variables(
        v.journal,
        BuildLsnAUIndex(image.tj, image.first), 
        image.first,
        MiniAllocator(map[], None)
      )
  }

  datatype Step =
      ReadForRecoveryStep(depth: nat)
    | FreezeForCommitStep(depth: nat)
    | ObserveFreshJournalStep()
    | PutStep()
    | DiscardOldStep()
    | InternalJournalMarshalStep(cut: LSN, addr: Address)
    | InternalMiniAllocatorFillStep()
    | InternalMiniAllocatorPruneStep()
    | InternalNoOpStep()
  {
    function I() : LikesJournal.Step
    {
      match this {
        case ReadForRecoveryStep(depth) => LikesJournal.ReadForRecoveryStep(depth)
        case FreezeForCommitStep(depth) => LikesJournal.FreezeForCommitStep(depth)
        case ObserveFreshJournalStep() => LikesJournal.ObserveFreshJournalStep()
        case PutStep() => LikesJournal.PutStep()
        case DiscardOldStep() => LikesJournal.DiscardOldStep()
        case InternalJournalMarshalStep(cut, addr) => LikesJournal.InternalJournalMarshalStep(cut, addr)
        case _ =>  LikesJournal.InternalNoOpStep()
      }
    }
  }

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case DiscardOldStep() => DiscardOld(v, v', lbl)
      case FreezeForCommitStep(_) => FreezeForCommit(v, v', lbl, step)
      case InternalJournalMarshalStep(_, _) => InternalJournalMarshal(v, v', lbl, step)
      case InternalMiniAllocatorFillStep() => InternalMiniAllocatorFill(v, v', lbl)
      case InternalMiniAllocatorPruneStep() => InternalMiniAllocatorPrune(v, v', lbl)
      case InternalNoOpStep() => InternalNoOp(v, v', lbl)
      case _ => OnlyAdvanceLikesJournal(v, v', lbl, step)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }
} // end module LikesJournal