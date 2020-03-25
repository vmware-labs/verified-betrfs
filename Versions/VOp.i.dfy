include "../MapSpec/UI.s.dfy"
include "../BlockCacheSystem/DiskLayout.i.dfy"

module ViewOp {
  import UI
  import opened DiskLayout

  type Loc = DiskLayout.Location

  // StatesView lives side-by-side with JournalView, together making
  // up the CompositeViews, but in many ways, StatesView is subservient
  // to JournalView. JournalView drives the syncing action,
  // and furthermore, JournalView is "incomplete" without StatesView
  // (as its journals are meaningless without states to base them
  // off of).

  datatype VOp =
    | StatesInternalOp
    | JournalInternalOp

    // This is where user-visible actions take place.
    // On the StatesView, we advance the ephemeral state forward.
    // From the JournalView side, this might be replaying something
    // from the journal or performing a new action.

    | AdvanceOp(uiop: UI.Op, replay: bool)

    // These describe the interaction between the StatesView
    // and the JournalView. The main interaction loop is, roughly:
    //
    // At initialization time, the JournalView sends the location of
    // the persistentIndirectionTable to the StatesView (although,
    // at this point, it's abstracted out to being just "the location
    // of the state")
    //
    // In order to update the indirection table, we do a
    // Freeze -> SendFrozenLoc -> CleanUp loop.
    //
    //  * Freeze: JournalView doesn't do anything other than mark
    //      that this is the place where the freeze took place.
    //      Meanwhile, the StatesView updates its frozen state to
    //      its ephemeral state.
    //
    //  * SendFrozenLoc: StatesView sends a loc to JournalView.
    //      It promises that the frozen state is now saved at that
    //      loc and will persist after crashing.
    //
    //  * CleanUp: JournalView promises to StatesView that it has now
    //      updated the superblock's pointer to the frozen location.
    //      StateView is now able to clean out its old persistent state
    //      and update it to its frozen state.

    | SendPersistentLocOp(loc: Loc)
    | FreezeOp
    | SendFrozenLocOp(loc: Loc)
    | CleanUpOp

    // Crash / syncing stuff. Syncing stuff is all handled
    // by JournalView.

    | CrashOp
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
    && (vop.StatesInternalOp? ==> uiop.NoOp?)
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
