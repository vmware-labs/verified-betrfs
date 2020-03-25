include "../MapSpec/UI.s.dfy"
include "../BlockCacheSystem/DiskLayout.i.dfy"

module VersionOp {
  import UI
  import opened DiskLayout

  type Loc = DiskLayout.Location

  // StateViews lives side-by-side with JournalViews, together making
  // up the CompositeViews, but in many ways, StateViews is subservient
  // to JournalViews. JournalViews drives the syncing action,
  // and furthermore, JournalViews is "incomplete" without StateViews
  // (as its journals are meaningless without states to base them
  // off of).

  datatype VOp =
    | TristateInternalOp
    | JournalInternalOp

    // This is where user-visible actions take place.
    // On the StateViews, we advance the ephemeral state forward.
    // From the JournalViews side, this might be replaying something
    // from the journal or performing a new action.

    | AdvanceOp(uiop: UI.Op, replay: bool)

    // These describe the interaction between the StateViews
    // and the JournalViews. The main interaction loop is, roughly:
    //
    // At initialization time, the JournalViews sends the location of
    // the persistentIndirectionTable to the StateViews (although,
    // at this point, it's abstracted out to being just "the location
    // of the state")
    //
    // In order to update the indirection table, we do a
    // Freeze -> SendFrozenLoc -> CleanUp loop.
    //
    //  * Freeze: JournalViews doesn't do anything other than mark
    //      that this is the place where the freeze took place.
    //      Meanwhile, the StateViews updates its frozen state to
    //      its ephemeral state.
    //
    //  * SendFrozenLoc: StateViews sends a loc to JournalViews.
    //      It promises that the frozen state is now saved at that
    //      loc and will persist after crashing.
    //
    //  * CleanUp: JournalViews promises to StateViews that it has now
    //      updated the superblock's pointer to the frozen location.
    //      StateView is now able to clean out its old persistent state
    //      and update it to its frozen state.

    | SendPersistentLocOp(loc: Loc)
    | FreezeOp
    | SendFrozenLocOp(loc: Loc)
    | CleanUpOp

    // Crash / syncing stuff. Syncing stuff is all handled
    // by JournalViews.

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
