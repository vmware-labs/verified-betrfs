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

  predicate VOpAgreesUIOp(vop: VOp, uiop: UIOp)
  {
    && (vop
  }
}
