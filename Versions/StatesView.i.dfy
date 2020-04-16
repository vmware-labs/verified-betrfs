include "../MapSpec/UIStateMachine.s.dfy"
include "../lib/Base/Option.s.dfy"
include "VOp.i.dfy"

abstract module StatesView {
  import SM : UIStateMachine

  import UI
  import opened Options
  import opened ViewOp

  datatype Constants = Constants(k: SM.Constants)
  datatype Variables = Variables(
      ghost disk: imap<Loc, SM.Variables>,
      ghost persistentLoc: Option<Loc>,
      ghost frozenLoc: Option<Loc>,
      ghost frozenState: Option<SM.Variables>,
      ghost ephemeralState: Option<SM.Variables>
  )

  predicate Init(k: Constants, s: Variables, loc: Loc)
  {
    && loc in s.disk
    && SM.Init(k.k, s.disk[loc])
    && s.persistentLoc == None
    && s.frozenLoc == None
    && s.frozenState == None
    && s.ephemeralState == None
  }

  datatype Step =
    | ObtainPersistentLocStep
    | AdvanceStep
    | CrashStep
    | FreezeStep
    | DiskChangeStep
    | ProvideFrozenLocStep
    | ForgetOldStep
    | StutterStep

  predicate ObtainPersistentLoc(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.SendPersistentLocOp?

    && s.persistentLoc.None?

    && s'.disk == s.disk
    && s'.persistentLoc == Some(vop.loc)
    && s'.frozenLoc == s.frozenLoc
    && s'.frozenState == s.frozenState
    && vop.loc in s.disk
    && SM.Inv(k.k, s.disk[vop.loc])
    && s'.ephemeralState == Some(s.disk[vop.loc])
  }

  predicate Advance(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.AdvanceOp?

    && s'.disk == s.disk
    && s'.persistentLoc == s.persistentLoc
    && s'.frozenLoc == s.frozenLoc
    && s'.frozenState == s.frozenState

    && s.ephemeralState.Some?
    && s'.ephemeralState.Some?
    && SM.Next(k.k, s.ephemeralState.value, s'.ephemeralState.value, vop.uiop)
  }

  predicate DiskChangesPreservesPersistentAndFrozen(
      s: Variables, s': Variables)
  {
    // We can modify `disk` in any way as we long as we don't
    // interfere with the state defined by persistentLoc
    // or frozenLoc.
    && (s.persistentLoc.None? ==>
      forall loc | loc in s.disk ::
          loc in s'.disk && s'.disk[loc] == s.disk[loc]
    )
    && (s.persistentLoc.Some? ==>
      && s.persistentLoc.Some?
      && s.persistentLoc.value in s.disk
      && s.persistentLoc.value in s'.disk
      && s'.disk[s.persistentLoc.value] == s.disk[s.persistentLoc.value]
    )
    && (s.frozenLoc.Some? ==>
      && s.frozenLoc.value in s.disk
      && s.frozenLoc.value in s'.disk
      && s'.disk[s.frozenLoc.value] == s.disk[s.frozenLoc.value]
    )
  }

  predicate Crash(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.CrashOp?

    && DiskChangesPreservesPersistentAndFrozen(s, s')
    && s'.persistentLoc == None
    && s'.frozenLoc == None
    && s'.frozenState == None
    && s'.ephemeralState == None
  }

  predicate Freeze(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.FreezeOp?

    && s'.disk == s.disk
    && s'.persistentLoc == s.persistentLoc
    && s'.frozenLoc == None
    && s'.frozenState == s.ephemeralState
    && s'.ephemeralState == s.ephemeralState
  }

  predicate DiskChange(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.StatesInternalOp?

    && DiskChangesPreservesPersistentAndFrozen(s, s')
    && s'.persistentLoc == s.persistentLoc
    && s'.frozenLoc == s.frozenLoc
    && s'.frozenState == s.frozenState
    && s'.ephemeralState == s.ephemeralState
  }

  predicate ProvideFrozenLoc(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.SendFrozenLocOp?

    && s.frozenLoc == None
    && s'.frozenLoc == Some(vop.loc)

    && s'.frozenState.Some?
    && s'.frozenLoc.value in s.disk
    && s.disk[s'.frozenLoc.value] == s'.frozenState.value

    && s'.disk == s.disk 
    && s'.persistentLoc == s.persistentLoc
    && s'.frozenState == s.frozenState
    && s'.ephemeralState == s.ephemeralState
  }

  predicate ForgetOld(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.CleanUpOp?

    && s'.disk == s.disk 
    && s'.persistentLoc == s.frozenLoc
    && s'.frozenLoc == None
    && s'.frozenState == None
    && s'.ephemeralState == s.ephemeralState
  }

  predicate Stutter(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && (vop.JournalInternalOp? || vop.StatesInternalOp? ||
        vop.PushSyncOp? || vop.PopSyncOp?)
    && s' == s
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, vop: VOp, step: Step)
  {
    match step {
      case ObtainPersistentLocStep => ObtainPersistentLoc(k, s, s', vop)
      case AdvanceStep => Advance(k, s, s', vop)
      case CrashStep => Crash(k, s, s', vop)
      case FreezeStep => Freeze(k, s, s', vop)
      case DiskChangeStep => DiskChange(k, s, s', vop)
      case ProvideFrozenLocStep => ProvideFrozenLoc(k, s, s', vop)
      case ForgetOldStep => ForgetOld(k, s, s', vop)
      case StutterStep => Stutter(k, s, s', vop)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, vop: VOp) {
    exists step :: NextStep(k, s, s', vop, step)
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && (s.persistentLoc.Some? ==>
        && s.persistentLoc.value in s.disk
        && SM.Inv(k.k, s.disk[s.persistentLoc.value]))
    && (s.frozenLoc.Some? ==>
        && s.frozenLoc.value in s.disk
        && SM.Inv(k.k, s.disk[s.frozenLoc.value]))
    //&& (forall loc | loc in s.disk :: SM.Inv(k.k, s.disk[loc]))
    && (s.frozenState.Some? ==> SM.Inv(k.k, s.frozenState.value))
    && (s.ephemeralState.Some? ==> SM.Inv(k.k, s.ephemeralState.value))
  }

  lemma InitImpliesInv(k: Constants, s: Variables, loc: Loc)
  requires Init(k, s, loc)
  ensures Inv(k, s)
  {
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp)
  requires Inv(k, s)
  requires Next(k, s, s', vop)
  ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', vop, step);
    match step {
      case ObtainPersistentLocStep => {
        assert Inv(k, s');
      }
      case AdvanceStep => {
        SM.NextPreservesInv(k.k,
          s.ephemeralState.value,
          s'.ephemeralState.value,
          vop.uiop);
        assert Inv(k, s');
      }
      case CrashStep => {
        assert Inv(k, s');
      }
      case FreezeStep => {
        assert Inv(k, s');
      }
      case DiskChangeStep => {
        assert Inv(k, s');
      }
      case ProvideFrozenLocStep => {
        assert Inv(k, s');
      }
      case ForgetOldStep => {
        assert Inv(k, s');
      }
      case StutterStep => {
        assert Inv(k, s');
      }
    }
  }
}
