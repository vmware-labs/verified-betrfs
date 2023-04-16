// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../Spec/MapSpec.s.dfy"
include "CoordinationJournal.i.dfy"
include "CoordinationBetree.i.dfy"

module CoordinationSystem {
  import opened Options
  import opened MapRemove_s
  import opened CrashTolerantMapSpecMod
//   import opened StampedMod
  import opened MsgHistoryMod
  import opened KeyType
  import opened ValueMessage
  import opened TotalKMMapMod
  import opened LSNMod
  import opened CoordinationJournal
  import opened CoordinationBetree

  import Async = CrashTolerantMapSpecMod.uiopifc.async
  type UIOp = CrashTolerantMapSpecMod.uiopifc.UIOp

  type SyncReqs = map<CrashTolerantMapSpecMod.uiopifc.SyncReqId, LSN>

  datatype Ephemeral =
    | Unknown
    | Known(
      progress: Async.EphemeralState,
      syncReqs: SyncReqs,
      mapLsn: LSN
    )
  {
  }

  datatype FreeSet = FreeSet(
    ephemeral: set<AU>, // should never include any AUs that are allocated to betree or journal
    inFlight: Option<set<AU>>,
    persistent: set<AU>
  ) {
    // TODO: this instead of au in ephemeral to deal with flushing of any cached block?
    function FreeToAlloc() : set<AU>
    {
      var free := ephemeral * persistent;
      if inFlight.Some? then free * inFlight.value else free
    }

    function UpdateEphemeral(allocs: set<AU>, deallocs: set<AU>) : FreeSet
      requires allocs <= ephemeral
      requires deallocs !! ephemeral
    {
      this.(ephemeral := ephemeral-allocs+deallocs)
    }

    function Freeze(unobserved: set<AU>) : FreeSet
      requires unobserved !! ephemeral
      requires inFlight.None?
    {
      this.(inFlight := Some(ephemeral + unobserved))
    }

    function CommitComplete(discard: set<AU>) : FreeSet
      requires inFlight.Some?
      requires discard !! ephemeral
    {
      FreeSet(ephemeral+discard, None, inFlight.value)
    }
  }

  // TODO: prove coordination system invariants and refinement
  // Inv
  //    how the freesets relate to betree/journal states [domains of the diskview]
  //    relationship amongst the diskviews (DVs always disjoint from xyz), they are congruent
  //    between ephemeral in flight and persistent some values may overlap
  //        ephemeral and persistent of tree same addr ==> same value (diskview)
  //    
  // When we need these invs: cache (one physcial DV, ghosty dv for the other)

  datatype Variables = Variables(
    journal: CoordinationJournal.Variables,
    betree: CoordinationBetree.Variables,
    ephemeral: Ephemeral,
    freeset: FreeSet
  )
  {
    predicate WF()
    {
      && journal.WF()
      && betree.WF()
      && (ephemeral.Known? == journal.ephemeral.Known? == betree.ephemeral.Known?)
      // Provable from invariant:
      && (journal.inFlight.Some? ==> betree.inFlight.Some?)
    }

    predicate Init(availAUs: set<AU>)
    {
      && CoordinationJournal.Init(journal)
      && CoordinationBetree.Init(betree)
      && ephemeral.Unknown?
      && freeset == FreeSet(availAUs, None, availAUs)
    }
  }

  predicate LoadEphemeralFromPersistent(v: Variables, v': Variables, uiop: UIOp)
  {
    && v.WF()
    && uiop.NoopOp?
    && v'.ephemeral.Known?
    && CoordinationJournal.Next(v.journal, v'.journal, CoordinationJournal.LoadEphemeralFromPersistentLabel())
    && CoordinationBetree.Next(v.betree, v'.betree, CoordinationBetree.LoadEphemeralFromPersistentLabel(v'.ephemeral.mapLsn))
    && v'.ephemeral.progress == Async.InitEphemeralState()
    && v'.ephemeral.syncReqs == map[]
    && v'.freeset == v.freeset.(ephemeral := v.freeset.persistent)
    // and thus all fields of v' are constrained.
  }

  // Move some journal state into the map to make it (closer to) fresh
  predicate Recover(v: Variables, v': Variables, uiop: UIOp, records: MsgHistory)
  {
    && uiop.NoopOp?
    && v.WF()
    && v.ephemeral.Known?
    && v'.WF()
    && v'.ephemeral.Known?

    && records.WF()

    // NB that Recover can interleave with betree steps (the Betree
    // reorganizing its state, possibly flushing stuff out to disk).
    && CoordinationJournal.Next(v.journal, v'.journal, CoordinationJournal.ReadForRecoveryLabel(records))
    && CoordinationBetree.Next(v.betree, v'.betree, CoordinationBetree.PutRecordsLabel(records))

    && v'.ephemeral == v.ephemeral.(mapLsn := records.seqEnd) 
    && v'.freeset == v.freeset
    // all else defined via predicates above
  }

  predicate AcceptRequest(v: Variables, v': Variables, uiop: UIOp)
  {
    && v.ephemeral.Known?
    && uiop.OperateOp?
    && uiop.baseOp.RequestOp?
    && uiop.baseOp.req !in v.ephemeral.progress.requests
    && v' == v.(ephemeral := v.ephemeral.(progress := v.ephemeral.progress.(
        requests := v.ephemeral.progress.requests + {uiop.baseOp.req})))
  }

  predicate Query(v: Variables, v': Variables, uiop: UIOp)
  {
    && v.WF()
    && v'.WF()
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
    && uiop.OperateOp?
    && uiop.baseOp.ExecuteOp?
    && uiop.baseOp.req.input.GetInput? // ensures that the uiop translates to a Get op
    && uiop.baseOp.reply.output.GetOutput?
    && uiop.baseOp.req in v.ephemeral.progress.requests
    && uiop.baseOp.reply.id == uiop.baseOp.req.id

    && uiop.baseOp.reply !in v.ephemeral.progress.replies
    && var key := uiop.baseOp.req.input.key;
    && var value := uiop.baseOp.reply.output.value;
    && assert AnyKey(key); // Line maybe unnecessary?

    // Journal confirms that the map is up-to-date (but otherwise doesn't do anything).
    && CoordinationJournal.Next(v.journal, v'.journal, CoordinationJournal.QueryEndLsnLabel(v.ephemeral.mapLsn))
    // Map handles the query
    && CoordinationBetree.Next(v.betree, v'.betree, CoordinationBetree.QueryLabel(v.ephemeral.mapLsn, key, value))

    && v'.ephemeral == v.ephemeral.(progress := v.ephemeral.progress.(
          requests := v.ephemeral.progress.requests - {uiop.baseOp.req},
          replies := v.ephemeral.progress.replies + {uiop.baseOp.reply}
      ))
  }

  predicate Put(v: Variables, v': Variables, uiop: UIOp)
  {
    && v.WF()
    && v'.WF()
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && uiop.OperateOp?
    && uiop.baseOp.ExecuteOp?
    && uiop.baseOp.req.input.PutInput? // ensures that the uiop translates to a put op
    && uiop.baseOp.reply.output.PutOutput?
    && uiop.baseOp.req in v.ephemeral.progress.requests
    && uiop.baseOp.reply.id == uiop.baseOp.req.id
    && uiop.baseOp.reply !in v.ephemeral.progress.replies

    && var key := uiop.baseOp.req.input.key;
    && var val := uiop.baseOp.req.input.value;

    && var singleton := MsgHistoryMod.SingletonAt(v.ephemeral.mapLsn, KeyedMessage(key, Define(val)));

    && v.WF()
    && CoordinationJournal.Next(v.journal, v'.journal, CoordinationJournal.PutLabel(singleton))
    && CoordinationBetree.Next(v.betree, v'.betree, CoordinationBetree.PutRecordsLabel(singleton))

    && v'.ephemeral == v.ephemeral.(
          mapLsn := v.ephemeral.mapLsn + 1,
          progress := v.ephemeral.progress.(
            requests := v.ephemeral.progress.requests - {uiop.baseOp.req},
            replies := v.ephemeral.progress.replies + {uiop.baseOp.reply}
          // syncReqs UNCHANGED
          )
      )
  }

  predicate DeliverReply(v: Variables, v': Variables, uiop: UIOp)
  {
    && v.ephemeral.Known?
    && uiop.OperateOp?
    && uiop.baseOp.ReplyOp?
    && uiop.baseOp.reply in v.ephemeral.progress.replies
    && v' == v.(ephemeral := v.ephemeral.(progress := v.ephemeral.progress.(
        replies := v.ephemeral.progress.replies - {uiop.baseOp.reply})))
  }

  // Journal Internal steps (writing stuff out to disk, for example)
  // and Betree Internal steps (writing stuff to disk, flushing and compacting,
  // which create new blocks in cache and rearrange the indirection table)
  // all look like stutters at this layer.

  predicate JournalInternal(v: Variables, v': Variables, uiop: UIOp, allocs: set<AU>, deallocs: set<AU>)
  {
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
    && uiop.NoopOp?

    && allocs <= v.freeset.FreeToAlloc()
    && deallocs !! v.freeset.ephemeral // journal further restrict deallocs to be things from the journal 

    && CoordinationJournal.Next(v.journal, v'.journal, CoordinationJournal.InternalLabel(allocs, deallocs))
    && v' == v.(
      journal := v'.journal, // predicate update above
      freeset := v.freeset.UpdateEphemeral(allocs, deallocs)
    )
  }

  predicate MapInternal(v: Variables, v': Variables, uiop: UIOp, allocs: set<AU>, deallocs: set<AU>)
  {
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
    && uiop.NoopOp?
    
    && allocs <= v.freeset.FreeToAlloc()
    && deallocs !! v.freeset.ephemeral // journal further restrict deallocs to be things from the journal 
    
    && CoordinationBetree.Next(v.betree, v'.betree, CoordinationBetree.InternalLabel(allocs, deallocs))
    && v' == v.(
      betree := v'.betree,
      freeset := v.freeset.UpdateEphemeral(allocs, deallocs)
    )  // predicate update above
  }

  predicate ReqSync(v: Variables, v': Variables, uiop: UIOp)
  {
    && v.WF()
    && v'.WF()
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
    && uiop.ReqSyncOp?
    && uiop.syncReqId !in v.ephemeral.syncReqs

    // TODO(robj): cleanup: delete this predicate; it's probably totally unecessary.
    // Need to record the current LSN, which is generally the current map state. But we
    // also need to confirm that the journal hasn't gone ahead, since sync is relative to
    // writes (which have affected the journal).
    && CoordinationJournal.Next(v.journal, v'.journal, CoordinationJournal.QueryEndLsnLabel(v.ephemeral.mapLsn))

    && var newEphemeral := v.ephemeral.(
        syncReqs := v.ephemeral.syncReqs[uiop.syncReqId := v.ephemeral.mapLsn]);

    // NB that the label for a sync in the table is the LSN AFTER the last write
    && v' == v.(
      journal := v'.journal, // admit relational update above
      ephemeral := newEphemeral
    ) 
  }

  predicate ReplySync(v: Variables, v': Variables, uiop: UIOp)
  {
    && v.WF()
    && v.ephemeral.Known?
    && uiop.ReplySyncOp?
    && uiop.syncReqId in v.ephemeral.syncReqs
    && CoordinationJournal.Next(v.journal, v'.journal,
      CoordinationJournal.QueryLsnPersistenceLabel(v.ephemeral.syncReqs[uiop.syncReqId]))
    && v' == v.(ephemeral := v.ephemeral.(
        syncReqs := MapRemove1(v.ephemeral.syncReqs, uiop.syncReqId)
      ))
  }

  predicate FreezeBetree(v: Variables, v': Variables, uiop: UIOp, unobservedJournal: set<AU>, unobservedBetree: set<AU>)
  {
    && uiop.NoopOp?
    && v.WF()
    && v.ephemeral.Known?
    && v.freeset.inFlight.None?
    && (unobservedJournal + unobservedBetree) !! v.freeset.ephemeral

    && CoordinationJournal.Next(v.journal, v'.journal, CoordinationJournal.FreezeAsLabel(unobservedJournal))
    && CoordinationBetree.Next(v.betree, v'.betree, CoordinationBetree.FreezeAsLabel(unobservedBetree))

    && v' == v.(
      journal := v'.journal, // admit relational update above
      betree := v'.betree,   // admit relational update above
      freeset := v.freeset.Freeze(unobservedJournal + unobservedBetree)
    )
  }

  // This step models issuing the superblock write
  predicate CommitStart(v: Variables, v': Variables, uiop: UIOp, newBoundaryLsn: LSN)
  {
    && uiop.NoopOp?
    && v.WF()
    && v.ephemeral.Known?
    && v.freeset.inFlight.Some? // has to start after a freezebetree step

    && CoordinationJournal.Next(v.journal, v'.journal, CoordinationJournal.CommitStartLabel(newBoundaryLsn, v.ephemeral.mapLsn))
    && CoordinationBetree.Next(v.betree, v'.betree, CoordinationBetree.CommitStartLabel(newBoundaryLsn))

    && v' == v.(
      journal := v'.journal, // admit relational update above
      betree := v'.betree   // admit relational update above
    )
  }

  // This step models learning that the outstanding superblock write has completed.
  predicate CommitComplete(v: Variables, v': Variables, uiop: UIOp, discardedJournal: set<AU>)
  {
    && v.WF()
    && v'.WF()
    && uiop.SyncOp?
    && v.ephemeral.Known? // provable from invariant
    && v.freeset.inFlight.Some?
    && discardedJournal !! v.freeset.ephemeral // provable from inv

    && CoordinationJournal.Next(v.journal, v'.journal, CoordinationJournal.CommitCompleteLabel(v.ephemeral.mapLsn, discardedJournal))
    && CoordinationBetree.Next(v.betree, v'.betree, CoordinationBetree.CommitCompleteLabel())

    && v' == v.(
      journal := v'.journal, // admit relational update above
      betree := v'.betree,   // admit relational update above
      freeset := v.freeset.CommitComplete(discardedJournal)
    )
  }

  predicate Crash(v: Variables, v': Variables, uiop: UIOp)
  {
    && v.WF()
    && v'.WF()
    && uiop.CrashOp?

    && CoordinationJournal.Next(v.journal, v'.journal, CoordinationJournal.CrashLabel())
    && CoordinationBetree.Next(v.betree, v'.betree, CoordinationBetree.CrashLabel())

    && v'.ephemeral.Unknown?
  }

  predicate Init(v: Variables, availAUs: set<AU>) {
    v.Init(availAUs)
  }

  datatype Step =
    | LoadEphemeralFromPersistentStep()
    | RecoverStep(records: MsgHistory)
    | AcceptRequestStep()
    | QueryStep()
    | PutStep()
    | DeliverReplyStep()
    | JournalInternalStep(allocs: set<AU>, deallocs: set<AU>)
    | MapInternalStep(allocs: set<AU>, deallocs: set<AU>)
    | ReqSyncStep()
    | ReplySyncStep()
    | FreezeBetreeStep(unobservedBetree: set<AU>, unobservedJournal: set<AU>)
    | CommitStartStep(newBoundaryLsn: LSN)
    | CommitCompleteStep(discardedJournal: set<AU>)
    | CrashStep()

  predicate NextStep(v: Variables, v': Variables, uiop: UIOp, step: Step) {
    match step {
      case LoadEphemeralFromPersistentStep() => LoadEphemeralFromPersistent(v, v', uiop)
      case RecoverStep(records) => Recover(v, v', uiop, records)
      case AcceptRequestStep() => AcceptRequest(v, v', uiop)
      case QueryStep() => Query(v, v', uiop)
      case PutStep() => Put(v, v', uiop)
      case DeliverReplyStep() => DeliverReply(v, v', uiop)
      case JournalInternalStep(allocs, deallocs) => JournalInternal(v, v', uiop, allocs, deallocs)
      case MapInternalStep(allocs, deallocs) => MapInternal(v, v', uiop, allocs, deallocs)
      case ReqSyncStep() => ReqSync(v, v', uiop)
      case ReplySyncStep() => ReplySync(v, v', uiop)
      case FreezeBetreeStep(unobservedBetree, unobservedJournal) => FreezeBetree(v, v', uiop, unobservedBetree, unobservedJournal)
      case CommitStartStep(newBoundaryLsn) => CommitStart(v, v', uiop, newBoundaryLsn)
      case CommitCompleteStep(discardedJournal) => CommitComplete(v, v', uiop, discardedJournal)
      case CrashStep() => Crash(v, v', uiop)
    }
  }

  predicate Next(v: Variables, v': Variables, uiop: UIOp) {
    exists step :: NextStep(v, v', uiop, step)
  }
}
