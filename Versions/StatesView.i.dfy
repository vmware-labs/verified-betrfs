// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../MapSpec/UIStateMachine.s.dfy"
include "../lib/Base/Option.s.dfy"
include "VOp.i.dfy"

// Abstraction of the cache/betree side of the system.

abstract module StatesView {
  import SM : UIStateMachine

  import UI
  import opened Options
  import opened ViewOp

  datatype Variables = Variables(
      ghost disk: imap<Loc, SM.Variables>,
      ghost persistentLoc: Option<Loc>,
      ghost frozenLoc: Option<Loc>,
      ghost frozenState: Option<SM.Variables>,
      ghost ephemeralState: Option<SM.Variables>
  )

  predicate Init(s: Variables, loc: Loc)
  {
    && loc in s.disk
    && SM.Init(s.disk[loc])
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

  predicate ObtainPersistentLoc(s: Variables, s': Variables, vop: VOp)
  {
    && vop.SendPersistentLocOp?

    && s.persistentLoc.None?

    && s'.disk == s.disk
    && s'.persistentLoc == Some(vop.loc)
    && s'.frozenLoc == s.frozenLoc
    && s'.frozenState == s.frozenState
    && vop.loc in s.disk
    && SM.Inv(s.disk[vop.loc])
    && s'.ephemeralState == Some(s.disk[vop.loc])
  }

  predicate Advance(s: Variables, s': Variables, vop: VOp)
  {
    && vop.AdvanceOp?

    && s'.disk == s.disk
    && s'.persistentLoc == s.persistentLoc
    && s'.frozenLoc == s.frozenLoc
    && s'.frozenState == s.frozenState

    && s.ephemeralState.Some?
    && s'.ephemeralState.Some?
    && SM.Next(s.ephemeralState.value, s'.ephemeralState.value, vop.uiop)
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

  predicate Crash(s: Variables, s': Variables, vop: VOp)
  {
    && vop.CrashOp?

    && DiskChangesPreservesPersistentAndFrozen(s, s')
    && s'.persistentLoc == None
    && s'.frozenLoc == None
    && s'.frozenState == None
    && s'.ephemeralState == None
  }

  predicate Freeze(s: Variables, s': Variables, vop: VOp)
  {
    && vop.FreezeOp?

    && s'.disk == s.disk
    && s'.persistentLoc == s.persistentLoc
    && s'.frozenLoc == None
    && s'.frozenState == s.ephemeralState
    && s'.ephemeralState == s.ephemeralState
  }

  predicate DiskChange(s: Variables, s': Variables, vop: VOp)
  {
    && vop.StatesInternalOp?

    && DiskChangesPreservesPersistentAndFrozen(s, s')
    && s'.persistentLoc == s.persistentLoc
    && s'.frozenLoc == s.frozenLoc
    && s'.frozenState == s.frozenState
    && s'.ephemeralState == s.ephemeralState
  }

  predicate ProvideFrozenLoc(s: Variables, s': Variables, vop: VOp)
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

  predicate ForgetOld(s: Variables, s': Variables, vop: VOp)
  {
    && vop.CleanUpOp?

    && s'.disk == s.disk 
    && s'.persistentLoc == s.frozenLoc
    && s'.frozenLoc == None
    && s'.frozenState == None
    && s'.ephemeralState == s.ephemeralState
  }

  predicate Stutter(s: Variables, s': Variables, vop: VOp)
  {
    && (vop.JournalInternalOp? || vop.StatesInternalOp? ||
        vop.PushSyncOp? || vop.PopSyncOp?)
    && s' == s
  }

  predicate NextStep(s: Variables, s': Variables, vop: VOp, step: Step)
  {
    match step {
      case ObtainPersistentLocStep => ObtainPersistentLoc(s, s', vop)
      case AdvanceStep => Advance(s, s', vop)
      case CrashStep => Crash(s, s', vop)
      case FreezeStep => Freeze(s, s', vop)
      case DiskChangeStep => DiskChange(s, s', vop)
      case ProvideFrozenLocStep => ProvideFrozenLoc(s, s', vop)
      case ForgetOldStep => ForgetOld(s, s', vop)
      case StutterStep => Stutter(s, s', vop)
    }
  }

  predicate Next(s: Variables, s': Variables, vop: VOp) {
    exists step :: NextStep(s, s', vop, step)
  }

  predicate Inv(s: Variables)
  {
    && (s.persistentLoc.Some? ==>
        && s.persistentLoc.value in s.disk
        && SM.Inv(s.disk[s.persistentLoc.value]))
    && (s.frozenLoc.Some? ==>
        && s.frozenLoc.value in s.disk
        && SM.Inv(s.disk[s.frozenLoc.value]))
    //&& (forall loc | loc in s.disk :: SM.Inv(s.disk[loc]))
    && (s.frozenState.Some? ==> SM.Inv(s.frozenState.value))
    && (s.ephemeralState.Some? ==> SM.Inv(s.ephemeralState.value))
  }

  lemma InitImpliesInv(s: Variables, loc: Loc)
  requires Init(s, loc)
  ensures Inv(s)
  {
  }

  lemma NextPreservesInv(s: Variables, s': Variables, vop: VOp)
  requires Inv(s)
  requires Next(s, s', vop)
  ensures Inv(s')
  {
    var step :| NextStep(s, s', vop, step);
    match step {
      case ObtainPersistentLocStep => {
        assert Inv(s');
      }
      case AdvanceStep => {
        SM.NextPreservesInv(
          s.ephemeralState.value,
          s'.ephemeralState.value,
          vop.uiop);
        assert Inv(s');
      }
      case CrashStep => {
        assert Inv(s');
      }
      case FreezeStep => {
        assert Inv(s');
      }
      case DiskChangeStep => {
        assert Inv(s');
      }
      case ProvideFrozenLocStep => {
        assert Inv(s');
      }
      case ForgetOldStep => {
        assert Inv(s');
      }
      case StutterStep => {
        assert Inv(s');
      }
    }
  }
}
