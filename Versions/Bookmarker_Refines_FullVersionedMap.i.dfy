include "Bookmarker.i.dfy"
include "../MapSpec/FullVersionedMap.s.dfy"

module Bookmarker_Refines_FullVersionedMap {
  import Bookmarker
  import FVM = FullVersionedMap
  import opened Options
  import opened Sequences
  import opened Journal
  import opened VersionOp
  import MapSpec
  import JournalChain

  function statesOf(m: MapSpec.Variables, jes: seq<JournalEntry>) : (res : seq<MapSpec.Variables>)
  ensures |res| == |jes| + 1
  ensures res[0] == m
  {
    if jes == [] then
      [m]
    else
      var p := statesOf(m, DropLast(jes));
      var m' := Last(p);
      var m1 := Bookmarker.Apply(m', Last(jes));
      p + [m1]
  }

  lemma Last_statesOf_ApplySeq(m: MapSpec.Variables, jes: seq<JournalEntry>)
  ensures Last(statesOf(m, jes)) == Bookmarker.ApplySeq(m, jes)

  function Ik(k: Bookmarker.Constants) : FVM.Constants
  {
    FVM.Constants(k.tsm.k)
  }

  function persistentState(k: Bookmarker.Constants, s: Bookmarker.Variables) : MapSpec.Variables
  requires Bookmarker.Inv(k, s)
  {
    s.tsm.disk[s.jc.persistentLoc]
  }

  function {:opaque} states(k: Bookmarker.Constants, s: Bookmarker.Variables)
      : (res : seq<MapSpec.Variables>)
  requires Bookmarker.Inv(k, s)
  ensures |res| == |s.jc.journal| + 1
      - (s.jc.persistentJournalIndex - s.jc.startVersion)
  {
    statesOf(persistentState(k, s), Bookmarker.JournalForPersistent(s))
        [s.jc.persistentJournalIndex - s.jc.persistentStateIndex ..]
  }

  function I(k: Bookmarker.Constants, s: Bookmarker.Variables) : FVM.Variables
  requires Bookmarker.Inv(k, s)
  {
    FVM.Variables(
      s.jc.persistentJournalIndex,
      states(k, s),
      s.jc.syncReqs
    )
  }

  lemma RefinesInit(k: Bookmarker.Constants, s: Bookmarker.Variables)
    requires Bookmarker.Init(k, s)
    ensures FVM.Init(Ik(k), I(k, s))
  {
    Bookmarker.reveal_JournalSuffix();
    reveal_states();
  }

  lemma SendPersistentLocRefines(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    requires vop.SendPersistentLocOp?
    ensures FVM.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert I(k, s).version == I(k, s').version;
    assert Bookmarker.JournalForPersistent(s)
        == Bookmarker.JournalForPersistent(s') by {
      Bookmarker.reveal_JournalSuffix();
    } 
    assert I(k, s).states == I(k, s').states by {
      assert persistentState(k, s) == persistentState(k, s');
      reveal_states();
    }
    assert FVM.NextStep(Ik(k), I(k, s), I(k, s'), uiop, FVM.StutterStep);
  }

  lemma ephemeralIsLast(k: Bookmarker.Constants, s: Bookmarker.Variables)
  requires s.jc.ephemeralStateIndex == s.jc.startVersion + |s.jc.journal|
  requires s.tsm.ephemeralState.Some?
  requires Bookmarker.Inv(k, s)
  ensures s.tsm.ephemeralState.value == Last(I(k, s).states);
  {
    calc {
      s.tsm.ephemeralState.value;
      Bookmarker.ApplySeq(persistentState(k, s), Bookmarker.JournalSlice(s, s.jc.persistentStateIndex, s.jc.ephemeralStateIndex));
      {
        Bookmarker.reveal_JournalSlice();
        Bookmarker.reveal_JournalSuffix();
        assert Bookmarker.JournalSlice(s, s.jc.persistentStateIndex, s.jc.ephemeralStateIndex)
            == Bookmarker.JournalForPersistent(s);
      }
      Bookmarker.ApplySeq(persistentState(k, s), Bookmarker.JournalForPersistent(s));
      {
        Last_statesOf_ApplySeq(persistentState(k, s), Bookmarker.JournalForPersistent(s));
      }
      Last(statesOf(persistentState(k, s), Bookmarker.JournalForPersistent(s)));
      {
        reveal_states();
      }
      Last(I(k, s).states);
    }
  }

  lemma AdvanceRefines(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    requires vop.AdvanceOp?
    ensures FVM.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    Bookmarker.reveal_JournalSuffix();

    if JournalChain.AdvanceEphemeral(k.jc, s.jc, s'.jc, vop) {
      assert MapSpec.Next(k.tsm.k,
        s.tsm.ephemeralState.value,
        s'.tsm.ephemeralState.value,
        uiop);

      assert Bookmarker.JournalForPersistent(s)
          == Bookmarker.JournalSlice(s, s.jc.persistentStateIndex, s.jc.ephemeralStateIndex)
        by {
          Bookmarker.reveal_JournalSlice();
        }

      ephemeralIsLast(k, s);

      var jes := JournalEntriesForUIOp(uiop);
      if |jes| == 0 {
        assert s'.jc.journal == s.jc.journal;
        assert s == s';
        assert I(k, s) == I(k, s');
        Last_statesOf_ApplySeq(persistentState(k, s), Bookmarker.JournalForPersistent(s));
        assert FVM.Query(Ik(k), I(k, s), I(k, s'), uiop);
        assert FVM.NextStep(Ik(k), I(k, s), I(k, s'), uiop, FVM.QueryStep);
      } else if |jes| == 1 {
        assert DropLast(Bookmarker.JournalForPersistent(s')) == Bookmarker.JournalForPersistent(s);
        assert Last(Bookmarker.JournalForPersistent(s')) == jes[0];

        assert Bookmarker.JournalForPersistent(s')
            == Bookmarker.JournalSlice(s', s'.jc.persistentStateIndex, s'.jc.ephemeralStateIndex)
          by { Bookmarker.reveal_JournalSlice(); }

        ephemeralIsLast(k, s');

        reveal_states();

        assert FVM.Advance(Ik(k), I(k, s), I(k, s'), uiop);
        assert FVM.NextStep(Ik(k), I(k, s), I(k, s'), uiop, FVM.AdvanceStep);
      } else {
        assert false;
      }

    } else if JournalChain.Replay(k.jc, s.jc, s'.jc, vop) {
      reveal_states();
      assert FVM.NextStep(Ik(k), I(k, s), I(k, s'), uiop, FVM.StutterStep);
    } else {
      assert false;
    }
  }

  lemma CrashRefines(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    requires vop.CrashOp?
    ensures FVM.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert FVM.Crash(Ik(k), I(k, s), I(k, s'), uiop);
    assert FVM.NextStep(Ik(k), I(k, s), I(k, s'), uiop, FVM.CrashStep);
  }

  lemma FreezeRefines(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    requires vop.FreezeOp?
    ensures FVM.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert FVM.NextStep(Ik(k), I(k, s), I(k, s'), uiop, FVM.StutterStep);
  }

  lemma TristateInternalRefines(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    requires vop.TristateInternalOp?
    ensures FVM.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert FVM.NextStep(Ik(k), I(k, s), I(k, s'), uiop, FVM.StutterStep);
  }

  lemma JournalInternalRefines(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    requires vop.JournalInternalOp?
    ensures FVM.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert FVM.NextStep(Ik(k), I(k, s), I(k, s'), uiop, FVM.StutterStep);
  }

  lemma SendFrozenLocRefines(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    requires vop.SendFrozenLocOp?
    ensures FVM.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert FVM.NextStep(Ik(k), I(k, s), I(k, s'), uiop, FVM.StutterStep);
  }

  lemma ForgetOldRefines(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    requires vop.ForgetOldOp?
    ensures FVM.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert FVM.NextStep(Ik(k), I(k, s), I(k, s'), uiop, FVM.StutterStep);
  }

  lemma PushSyncRefines(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    requires vop.PushSyncOp?
    ensures FVM.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert FVM.NextStep(Ik(k), I(k, s), I(k, s'), uiop, FVM.PushSyncStep(vop.id));
  }

  lemma PopSyncRefines(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    requires vop.PopSyncOp?
    ensures FVM.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert FVM.NextStep(Ik(k), I(k, s), I(k, s'), uiop, FVM.PopSyncStep(vop.id));
  }

  lemma RefinesNextStep(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    ensures FVM.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    match vop {
      case SendPersistentLocOp(loc) => { SendPersistentLocRefines(k, s, s', uiop, vop); }
      case AdvanceOp(uiop, replay) => { AdvanceRefines(k, s, s', uiop, vop); }
      case CrashOp => { CrashRefines(k, s, s', uiop, vop); }
      case FreezeOp => { FreezeRefines(k, s, s', uiop, vop); }
      case TristateInternalOp => { TristateInternalRefines(k, s, s', uiop, vop); }
      case JournalInternalOp => { JournalInternalRefines(k, s, s', uiop, vop); }
      case SendFrozenLocOp(loc) => { SendFrozenLocRefines(k, s, s', uiop, vop); }
      case ForgetOldOp => { ForgetOldRefines(k, s, s', uiop, vop); }
      case PushSyncOp(id) => { PushSyncRefines(k, s, s', uiop, vop); }
      case PopSyncOp(id) => { PopSyncRefines(k, s, s', uiop, vop); }
    }
  }

  lemma RefinesNext(k: Bookmarker.Constants, s: Bookmarker.Variables, s': Bookmarker.Variables, uiop: UI.Op)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Next(k, s, s', uiop)
    ensures Bookmarker.Inv(k, s')
    ensures FVM.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    var vop :| Bookmarker.NextStep(k, s, s', vop, uiop);
    RefinesNextStep(k, s, s', uiop, vop);
  }
}
