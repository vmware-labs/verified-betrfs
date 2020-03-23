include "../MapSpec/UI.s.dfy"
include "../BlockCacheSystem/DiskLayout.i.dfy"

module VersionOp {
  import UI
  import opened DiskLayout

  type Loc = DiskLayout.Location

  datatype VOp =
    | SendPersistentLocOp(loc: Loc)
    | AdvanceOp(uiop: UI.Op, replay: bool)
    | CrashOp
    | FreezeOp
    | TristateInternalOp
    | JournalInternalOp
    | SendFrozenLocOp(loc: Loc)
    | CleanUpOp
    | PushSyncOp(ghost id: int)
    | PopSyncOp(ghost id: int)

  predicate VOpAgreesUIOp(vop: VOp, uiop: UI.Op)
  {
    && (vop.SendPersistentLocOp? ==> uiop.NoOp?)
    && (vop.AdvanceOp? ==>
        && (vop.replay ==> uiop.NoOp?)
        && (!vop.replay ==> uiop == vop.uiop)
    )
    && (vop.CrashOp? ==> uiop.CrashOp?)
    && (vop.FreezeOp? ==> uiop.NoOp?)
    && (vop.TristateInternalOp? ==> uiop.NoOp?)
    && (vop.JournalInternalOp? ==> uiop.NoOp?)
    && (vop.SendFrozenLocOp? ==> uiop.NoOp?)
    && (vop.CleanUpOp? ==> uiop.NoOp?)
    && (vop.PushSyncOp? ==>
      && uiop.PushSyncOp?
      && uiop.id == vop.id
    )
    && (vop.PopSyncOp? ==>
      && uiop.PopSyncOp?
      && uiop.id == vop.id
    )
  }
}
