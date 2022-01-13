include "../../lib/Base/MapRemove.s.dfy"
include "../MsgHistory.i.dfy"
include "../../Spec/MapSpec.s.dfy"

module JournalInterpTypeMod {
  import opened MapRemove_s
  import MapSpecMod
  import CrashTolerantMapSpecMod
  import opened MsgHistoryMod

  // TODO now that we've pulled all the ephemeral gunk out of here, any reason to keep this wrapper?
  // Maybe we can strip this down to msgSeq in CoordProgramMod (just as base map is an Interp).

  import Async = CrashTolerantMapSpecMod.async

  function VersionFor(base: InterpMod.Interp, v: Variables) : CrashTolerantMapSpecMod.Version
    requires v.WF()
    requires v.msgSeq.CanFollow(base.seqEnd)
  {
    var mapspec := MapSpecMod.Variables(v.msgSeq.ApplyToInterp(base));
    CrashTolerantMapSpecMod.Version(Async.PersistentState(mapspec))
  }

  datatype Variables = Variables(msgSeq: MsgSeq)
  {
    predicate WF() {
      && msgSeq.WF()
    }

    predicate CanFollow(lsn: LSN)
    {
      msgSeq.CanFollow(lsn)
    }

    function VersionsFromBase(base: InterpMod.Interp) : seq<CrashTolerantMapSpecMod.Version>
      requires WF()
      requires CanFollow(base.seqEnd)
    {
      var numVersions := msgSeq.Len()+1;  // Can apply zero to Len() messages.
      seq(msgSeq.Len()+1, i requires 0 <= i < numVersions =>
        VersionFor(base, PruneTail(i + msgSeq.seqStart)))
    }

    predicate CanPruneTo(lsn: LSN)
    {
      // NB Pruning allows one more LSN than Contains, because you can PruneHead
      // all the way to seqEnd (and get an empty) (or PruneTail all the way to
      // seqStart).
      msgSeq.seqStart <= lsn <= msgSeq.seqEnd
    }

    function PruneHead(lsn: LSN) : Variables
      requires WF()
      requires CanPruneTo(lsn)
    {
      Variables(msgSeq.PruneHead(lsn))
    }

    function PruneTail(lsn: LSN) : Variables
      requires WF()
      requires CanPruneTo(lsn)
    {
      Variables(msgSeq.PruneTail(lsn))
    }

    function Concat(tail: MsgSeq) : Variables
      requires WF()
      requires tail.WF()
      requires msgSeq.seqEnd == tail.seqStart
    {
      Variables(msgSeq.Concat(tail))
    }
  }

  function Mkfs() : Variables
  {
    Variables(MsgHistoryMod.Empty())
  }
} // module
