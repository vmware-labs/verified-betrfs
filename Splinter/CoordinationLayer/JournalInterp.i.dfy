include "../../lib/Base/MapRemove.s.dfy"
include "../MsgHistory.i.dfy"
include "../../Spec/MapSpec.s.dfy"

module JournalInterpTypeMod {
  import opened MapRemove_s
  import MapSpecMod
  import CrashTolerantMapSpecMod
  import opened MsgHistoryMod

  datatype Variables = Variables(msgSeq: MsgSeq, syncReqs: map<CrashTolerantMapSpecMod.SyncReqId, LSN>)
  {
    predicate WF() {
      && msgSeq.WF()
    }

    function SyncReqsAt(lsn: LSN) : set<CrashTolerantMapSpecMod.SyncReqId>
      requires WF()
    {
      set id | id in syncReqs && syncReqs[id] == lsn
    }
    
    function VersionFor(base: InterpMod.Interp, lsn: LSN) : CrashTolerantMapSpecMod.Version
      requires WF()
      requires base.seqEnd == msgSeq.seqStart
      requires msgSeq.seqStart <= lsn <= msgSeq.seqEnd
    {
      // TODO No accounting for v.syncReqs < boundaryLSN; hrmm.
      var mapspec := MapSpecMod.Variables(msgSeq.Truncate(lsn).ApplyToInterp(base));
      var asyncmapspec := CrashTolerantMapSpecMod.async.Variables(mapspec, {}, {}); // TODO um, no reqs & replies!?
      CrashTolerantMapSpecMod.Version(asyncmapspec, SyncReqsAt(lsn))
    }

    function VersionsFromBase(base: InterpMod.Interp) : seq<CrashTolerantMapSpecMod.Version>
      requires WF()
      requires base.seqEnd == msgSeq.seqStart
    {
      var numVersions := msgSeq.Len()+1;  // Can apply zero to Len() messages.
      seq(msgSeq.Len()+1, i requires 0 <= i < numVersions => VersionFor(base, i + msgSeq.seqStart))
    }

    function AsCrashTolerantMapSpec(base: InterpMod.Interp) : CrashTolerantMapSpecMod.Variables
      requires WF()
      requires base.seqEnd == msgSeq.seqStart
    {
      CrashTolerantMapSpecMod.Variables(VersionsFromBase(base), 0)  // 0 is always the stable idx; why do we allow others in spec?
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
