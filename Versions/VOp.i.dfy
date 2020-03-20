include "../MapSpec/UI.s.dfy"

module VersionOp {
  import UI

  datatype Location = Loc1 | Loc2

  datatype VOp =
    | SendPersistentLocOp(loc: Location)
    | AdvanceOp(uiop: UI.Op, replay: bool)
    | CrashOp
    | FreezeOp
    | TristateInternalOp
    | JournalInternalOp
    | SendFrozenLocOp(loc: Location)
    | ForgetOldOp
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
    && (vop.ForgetOldOp? ==> uiop.NoOp?)
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
