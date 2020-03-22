include "TristateMap.i.dfy"
include "JournalChain.i.dfy"

// Combine TriStateMap and JournalChain.

module Bookmarker {
  import TriStateMap
  import JournalChain
  import SM = MapSpec
  import opened VersionOp
  import opened Options
  import opened Journal
  import opened Sequences

  import UI

  datatype Constants = Constants(
      tsm: TriStateMap.Constants,
      jc: JournalChain.Constants)

  datatype Variables = Variables(
      tsm: TriStateMap.Variables,
      jc: JournalChain.Variables)

  datatype Step = Step(vop: VOp) 

  predicate Init(k: Constants, s: Variables)
  {
    && TriStateMap.Init(k.tsm, s.tsm)
    && JournalChain.Init(k.jc, s.jc)
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  {
    && TriStateMap.Next(k.tsm, s.tsm, s'.tsm, vop)
    && JournalChain.Next(k.jc, s.jc, s'.jc, vop)
    && VOpAgreesUIOp(vop, uiop)
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UI.Op)
  {
    exists step: Step :: NextStep(k, s, s', step.vop, uiop)
  }

  /// Invariant definition

  predicate IsPath(
      k: SM.Constants,
      s: SM.Variables,
      uiops: seq<SM.UIOp>,
      s': SM.Variables,
      states: seq<SM.Variables>)
  {
    && |states| == |uiops| + 1
    && states[0] == s
    && states[|states|-1] == s'
    && forall i | 0 <= i < |uiops| ::
        SM.Next(k, states[i], states[i+1], uiops[i])
  }

  predicate path(
      k: SM.Constants,
      s: SM.Variables,
      jes: seq<JournalEntry>,
      s': SM.Variables)
  {
    exists states, uiops ::
        && jes == JournalEntriesForUIOps(uiops)
        && IsPath(k, s, uiops, s', states)
  }

  predicate IsSuffix<T>(s: seq<T>, t: seq<T>)
  {
    && |t| <= |s|
    && s[|s| - |t| ..] == t
  }

  // Sequence subtraction s-t
  // Only makes sense when t is a suffix of s.
  // Result is that s-t+t == s for the usual notion
  // of sequence addition.
  function {:opaque} SeqSub<T>(s: seq<T>, t: seq<T>) : seq<T>
  requires IsSuffix(s, t)
  ensures SeqSub(s, t) + t == s
  {
    s[.. |s| - |t|]
  }

  lemma SeqSubAdd<T>(a: seq<T>, b: seq<T>, c: seq<T>, d: seq<T>)
  requires IsSuffix(a, b)
  requires IsSuffix(b + c, d)
  ensures SeqSub(a, b) + SeqSub(b + c, d)
      == SeqSub(a + c, d)
  {
    reveal_SeqSub();
  }

  predicate advances(k: SM.Constants,
      s: SM.Variables,
      jes: seq<JournalEntry>, 
      s': SM.Variables,
      jes2: seq<JournalEntry>)
  {
    && IsSuffix(jes, jes2)
    && path(k, s, SeqSub(jes, jes2), s')
  }

  function s1(s: Variables) : SM.Variables
  requires s.jc.persistentLoc in s.tsm.disk
  {
    s.tsm.disk[s.jc.persistentLoc]
  }

  function s2(s: Variables) : SM.Variables
  requires s.jc.persistentLoc in s.tsm.disk
  {
    if s.tsm.frozenState.Some? then
      s.tsm.frozenState.value
    else
      s1(s)
  }

  function s3(s: Variables) : SM.Variables
  requires s.jc.persistentLoc in s.tsm.disk
  {
    if s.tsm.ephemeralState.Some? then
      s.tsm.ephemeralState.value
    else
      s1(s)
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && (s.jc.frozenLoc.Some? ==>
      && s.tsm.frozenLoc == s.jc.frozenLoc
    )
    && (s.tsm.persistentLoc.Some? ==>
      || s.tsm.persistentLoc.value == s.jc.persistentLoc
      || s.tsm.frozenLoc == Some(s.jc.persistentLoc)
    )
    && (s.tsm.frozenLoc.Some? ==>
      && s.tsm.frozenLoc.value in s.tsm.disk
      && s.tsm.frozenState.Some?
      && s.tsm.disk[s.tsm.frozenLoc.value]
          == s.tsm.frozenState.value
    )
    && (s.tsm.frozenState.Some? ==>
      s.tsm.ephemeralState.Some?
    )
    && (s.tsm.ephemeralState.Some? ==>
      s.tsm.persistentLoc.Some?
    )
    && s.jc.persistentLoc in s.tsm.disk

    && SM.Inv(k.tsm.k, s1(s))
    && SM.Inv(k.tsm.k, s2(s))
    && SM.Inv(k.tsm.k, s3(s))

    && advances(k.tsm.k, s1(s), s.jc.j_gamma, s2(s), s.jc.j2)
    && advances(k.tsm.k, s2(s), s.jc.j2 + s.jc.j_delta, s3(s), s.jc.j3)
  }

  lemma path_empty(k: SM.Constants, s: SM.Variables)
  ensures path(k, s, [], s)
  {
    var states := [s];
    var uiops := [];
    assert [] == JournalEntriesForUIOps(uiops);
    assert IsPath(k, s, uiops, s, states);
  }

  lemma paths_compose(k: SM.Constants, s1: SM.Variables, jes1: seq<JournalEntry>, s2: SM.Variables, jes2: seq<JournalEntry>, s3: SM.Variables)
  requires path(k, s1, jes1, s2)
  requires path(k, s2, jes2, s3)
  ensures path(k, s1, jes1 + jes2, s3)
  {
    var states1, uiops1 :|
        && jes1 == JournalEntriesForUIOps(uiops1)
        && IsPath(k, s1, uiops1, s2, states1);
    var states2, uiops2 :|
        && jes2 == JournalEntriesForUIOps(uiops2)
        && IsPath(k, s2, uiops2, s3, states2);

    var states := states1 + states2[1..];
    var uiops := uiops1 + uiops2;

    JournalEntriesForUIOpsAdditive(uiops1, uiops2);
    assert jes1 + jes2 == JournalEntriesForUIOps(uiops);

    forall i | 0 <= i < |uiops|
    ensures SM.Next(k, states[i], states[i+1], uiops[i]);
    {
      if i < |uiops1| {
        assert states[i] == states1[i];
        assert states[i+1] == states1[i+1];
        assert uiops[i] == uiops1[i];
        assert SM.Next(k, states1[i], states1[i+1], uiops1[i]);
      } else {
        assert states[i] == states2[i - |uiops1|];
        assert states[i+1] == states2[i - |uiops1| + 1];
        assert uiops[i] == uiops2[i - |uiops1|];
        assert SM.Next(k, states2[i - |uiops1|],
            states2[i - |uiops1| + 1], uiops2[i - |uiops1|]);
      }
    }
    assert IsPath(k, s1, uiops, s3, states);
  }

  lemma path_append(k: SM.Constants, s1: SM.Variables, jes: seq<JournalEntry>, s2: SM.Variables, uiop: SM.UIOp, s3: SM.Variables)
  requires path(k, s1, jes, s2)
  requires SM.Next(k, s2, s3, uiop)
  ensures path(k, s1, jes + JournalEntriesForUIOp(uiop), s3)
  {
    var jes2 := JournalEntriesForUIOp(uiop);
    assert jes2 == JournalEntriesForUIOps([uiop]);
    assert IsPath(k, s2, [uiop], s3, [s2, s3]);
    assert path(k, s2, jes2, s3);
    paths_compose(k, s1, jes, s2, jes2, s3);
  }

  lemma InitImpliesInv(k: Constants, s: Variables, s': Variables)
  requires Init(k, s)
  ensures Inv(k, s)
  {
    SM.InitImpliesInv(k.tsm.k, s1(s));
    path_empty(k.tsm.k, s1(s));
  }

  lemma Move3PreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires vop.AdvanceOp?
  requires JournalChain.Move3(k.jc, s.jc, s'.jc, vop)
  requires TriStateMap.Advance(k.tsm, s.tsm, s'.tsm, vop)
  requires Inv(k, s)
  ensures Inv(k, s')
  {
    SM.NextPreservesInv(k.tsm.k, s3(s), s3(s'), vop.uiop);
    var new_je := JournalEntriesForUIOp(vop.uiop);
    path_append(k.tsm.k, s2(s), s.jc.j2 + s.jc.j_delta, s3(s), vop.uiop, s3(s'));

    assert s1(s) == s1(s');
    assert s2(s) == s2(s');

    assert s.jc.j3 == [];
    assert SeqSub(s.jc.j2 + s.jc.j_delta, s.jc.j3)
        == s.jc.j2 + s.jc.j_delta;
    assert SeqSub(s.jc.j2 + s.jc.j_delta + JournalEntriesForUIOp(vop.uiop), s.jc.j3)
        == s.jc.j2 + s.jc.j_delta + JournalEntriesForUIOp(vop.uiop);

    assert path(k.tsm.k, s2(s), s.jc.j2 + s.jc.j_delta + new_je, s3(s'));
    assert path(k.tsm.k, s2(s'), SeqSub(s'.jc.j2 + s'.jc.j_delta, s'.jc.j3), s3(s'));
    assert advances(k.tsm.k, s2(s'), s'.jc.j2 + s'.jc.j_delta, s3(s'), s'.jc.j3);

    assert Inv(k, s');
  }

  lemma ReplayPreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires vop.AdvanceOp?
  requires JournalChain.Replay(k.jc, s.jc, s'.jc, vop)
  requires TriStateMap.Advance(k.tsm, s.tsm, s'.tsm, vop)
  requires Inv(k, s)
  ensures Inv(k, s')
  {
    SM.NextPreservesInv(k.tsm.k, s3(s), s3(s'), vop.uiop);
    path_append(k.tsm.k, s2(s), SeqSub(s.jc.j2 + s.jc.j_delta, s.jc.j3), s3(s), vop.uiop, s3(s'));
    assert SeqSub(s.jc.j2 + s.jc.j_delta, s.jc.j3) + JournalEntriesForUIOp(vop.uiop)
        == SeqSub(s.jc.j2 + s.jc.j_delta, s'.jc.j3);
    assert Inv(k, s');
  }

  lemma AdvancePreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires NextStep(k, s, s', vop, uiop)
  requires vop.AdvanceOp?
  requires Inv(k, s)
  ensures Inv(k, s')
  {
    if JournalChain.Move3(k.jc, s.jc, s'.jc, vop) {
      Move3PreservesInv(k, s, s', vop, uiop);
    } else if JournalChain.Replay(k.jc, s.jc, s'.jc, vop) {
      ReplayPreservesInv(k, s, s', vop, uiop);
    }
  }

  lemma FreezePreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires NextStep(k, s, s', vop, uiop)
  requires vop.FreezeOp?
  requires Inv(k, s)
  ensures Inv(k, s')
  {
    path_empty(k.tsm.k, s2(s));
    path_empty(k.tsm.k, s3(s));
    paths_compose(k.tsm.k, s1(s),
        SeqSub(s.jc.j_gamma, s.jc.j2),
        s2(s),
        SeqSub(s.jc.j2 + s.jc.j_delta, s.jc.j3),
        s3(s));
    SeqSubAdd(s.jc.j_gamma, s.jc.j2, s.jc.j_delta, s.jc.j3);
    assert SeqSub(s.jc.j_gamma, s.jc.j2) + SeqSub(s.jc.j2 + s.jc.j_delta, s.jc.j3)
        == SeqSub(s.jc.j_gamma + s.jc.j_delta, s.jc.j3);
    assert advances(k.tsm.k, s1(s), s.jc.j_gamma + s.jc.j_delta, s3(s), s.jc.j3);
  }

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires NextStep(k, s, s', vop, uiop)
  requires Inv(k, s)
  ensures Inv(k, s')
  {
    var tsm_step :| TriStateMap.NextStep(k.tsm, s.tsm, s'.tsm, vop, tsm_step);
    var jc_step :| JournalChain.NextStep(k.jc, s.jc, s'.jc, vop, jc_step);

    match vop {
      case SendPersistentLocOp(loc) => { }
      case AdvanceOp(_, _) => {
        AdvancePreservesInv(k, s, s', vop, uiop);
      }
      case CrashOp => {
        path_empty(k.tsm.k, s1(s));
        assert s1(s) == s1(s') == s2(s') == s3(s');
        assert JournalChain.Crash(k.jc, s.jc, s'.jc, vop);
        assert TriStateMap.Crash(k.tsm, s.tsm, s'.tsm, vop);
      }
      case FreezeOp => {
        FreezePreservesInv(k, s, s', vop, uiop);
      }
      case TristateInternalOp => { }
      case JournalInternalOp => {
        assert s.tsm == s'.tsm;
        if JournalChain.Move1to2(k.jc, s.jc, s'.jc, vop) {
          assert Inv(k, s');
        }
        else if JournalChain.ExtendLog1(k.jc, s.jc, s'.jc, vop) {
          assert Inv(k, s');
        }
        else if JournalChain.ExtendLog2(k.jc, s.jc, s'.jc, vop) {
          assert Inv(k, s');
        }
        else {
          assert s.jc == s'.jc;
        }
      }
      case SendFrozenLocOp(loc) => { }
      case CleanUpOp => {
        assert JournalChain.CleanUp(k.jc, s.jc, s'.jc, vop);
        assert TriStateMap.ForgetOld(k.tsm, s.tsm, s'.tsm, vop);
        assert Inv(k, s');
      }
      case PushSyncOp(id) => { }
      case PopSyncOp(id) => { }
    }
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UI.Op)
  requires Next(k, s, s', uiop)
  requires Inv(k, s)
  ensures Inv(k, s')
  {
    var step: Step :| NextStep(k, s, s', step.vop, uiop);
    NextStepPreservesInv(k, s, s', step.vop, uiop);
  }
}
