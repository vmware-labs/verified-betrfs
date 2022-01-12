include "../../lib/Base/MapRemove.s.dfy"
include "../MsgHistory.i.dfy"
include "../../Spec/MapSpec.s.dfy"

module JournalInterpTypeMod {
  import opened MapRemove_s
  import MapSpecMod
  import CrashTolerantMapSpecMod
  import opened MsgHistoryMod

  type SyncReqs = map<CrashTolerantMapSpecMod.SyncReqId, LSN>

  function BeheadSyncReqs(sr: SyncReqs, lsn: LSN) : SyncReqs
  {
    map k | k in sr && lsn <= sr[k] :: sr[k]
  }

  function TruncateSyncReqs(sr: SyncReqs, lsn: LSN) : SyncReqs
  {
    map k | k in sr && sr[k] < lsn :: sr[k]
  }

  datatype Variables = Variables(msgSeq: MsgSeq, syncReqs: SyncReqs)
  {
    predicate WF() {
      && msgSeq.WF()
    }

    function SyncReqsAt(lsn: LSN) : set<CrashTolerantMapSpecMod.SyncReqId>
      requires WF()
    {
      set id | id in syncReqs && syncReqs[id] == lsn
    }

    predicate CanFollow(lsn: LSN)
    {
      || msgSeq.IsEmpty()
      || msgSeq.seqStart == lsn
    }

    // NB Pruning (Behead or Truncate) allows one more LSN than Contains,
    // because you can Behead all the way to seqEnd (and get an empty)
    // (or Truncate all the way to seqStart).
    predicate CanPruneTo(lsn: LSN)
    {
      msgSeq.seqStart <= lsn <= msgSeq.seqEnd
    }
    
    function VersionFor(base: InterpMod.Interp, lsn: LSN) : CrashTolerantMapSpecMod.Version
      requires WF()
      requires CanFollow(base.seqEnd)
      requires CanPruneTo(lsn)
    {
      // TODO No accounting for v.syncReqs < boundaryLSN; hrmm.
      var mapspec := MapSpecMod.Variables(msgSeq.Truncate(lsn).ApplyToInterp(base));
      var asyncmapspec := CrashTolerantMapSpecMod.async.Variables(mapspec, {}, {}); // TODO um, no reqs & replies!?
      CrashTolerantMapSpecMod.Version(asyncmapspec, SyncReqsAt(lsn))
    }

    function VersionsFromBase(base: InterpMod.Interp) : seq<CrashTolerantMapSpecMod.Version>
      requires WF()
      requires CanFollow(base.seqEnd)
    {
      var numVersions := msgSeq.Len()+1;  // Can apply zero to Len() messages.
      seq(msgSeq.Len()+1, i requires 0 <= i < numVersions => VersionFor(base, i + msgSeq.seqStart))
    }

    function AsCrashTolerantMapSpec(base: InterpMod.Interp) : CrashTolerantMapSpecMod.Variables
      requires WF()
      requires CanFollow(base.seqEnd)
    {
      CrashTolerantMapSpecMod.Variables(VersionsFromBase(base), 0)  // 0 is always the stable idx; why do we allow others in spec?
    }

    function Behead(lsn: LSN) : Variables
      requires WF()
      requires CanPruneTo(lsn)
    {
      Variables(msgSeq.Behead(lsn), BeheadSyncReqs(syncReqs, lsn))
    }

    function Truncate(lsn: LSN) : Variables
      requires WF()
      requires CanPruneTo(lsn)
    {
      Variables(msgSeq.Truncate(lsn), TruncateSyncReqs(syncReqs, lsn))
    }

    function DropSyncReqs() : Variables
    {
      Variables(msgSeq, map[])
    }
  }

  predicate ReqSync(v: Variables, v': Variables, syncReqId: CrashTolerantMapSpecMod.SyncReqId)
  {
    && 0 < v.msgSeq.seqEnd
    && syncReqId !in v.syncReqs.Keys
    && v' == v.(syncReqs := v.syncReqs[syncReqId := v.msgSeq.seqEnd-1])
  }

  predicate CompleteSync(v: Variables, v': Variables, syncReqId: CrashTolerantMapSpecMod.SyncReqId)
  {
    && syncReqId in v.syncReqs.Keys
    //&& v.syncReqs[syncReqId] < v.persistentLSN  // TODO! hidden state for this model.
    && v' == v.(syncReqs := MapRemove1(v.syncReqs, syncReqId))
  }

  function Mkfs() : Variables
  {
    Variables(MsgHistoryMod.Empty(), map[])
  }
} // module
