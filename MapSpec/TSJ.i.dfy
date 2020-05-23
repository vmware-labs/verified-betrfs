include "../MapSpec/MapSpec.s.dfy"
include "../MapSpec/UIStateMachine.s.dfy"
include "../lib/Base/Maps.s.dfy"
include "../MapSpec/ThreeStateVersioned.s.dfy"
include "Journal.i.dfy"

// TSJ = Three-State-Journaled.
// There are three states, and each one has a journal.
// We also track two extra journals ("gamma" and "delta")
// which describe the relationships between the three
// states.

abstract module TSJ {
  import SM : UIStateMachine

  import opened Maps
  import UI
  import opened ThreeStateTypes
  import opened Journal

  datatype Constants = Constants(k: SM.Constants)

  // s1 -------> t1
  //       j1
  //
  //                   s2 -------> t2
  //                         j2
  //
  //                                      s3 -------> t3
  //                                            j3
  //
  //   -------------------------->  ---------------->
  //              gamma                   delta

  datatype Variables = Variables(
      s1: SM.Variables,
      s2: SM.Variables,
      s3: SM.Variables,
      j1: seq<JournalEntry>,
      j2: seq<JournalEntry>,
      j3: seq<JournalEntry>,
      j_gamma: seq<JournalEntry>,
      j_delta: seq<JournalEntry>,
      ghost outstandingSyncReqs: map<int, SyncReqStatus>
  )

  predicate Init(k: Constants, s: Variables)
  {
    && SM.Init(k.k, s.s1)
    && s.s2 == s.s1
    && s.s3 == s.s1
    && s.j1 == []
    && s.j2 == []
    && s.j3 == []
    && s.j_gamma == []
    && s.j_delta == []
    && s.outstandingSyncReqs == map[]
  }

  datatype Step =
    | CrashStep
    | Move1to2Step
    | Move2to3Step
    | ExtendLog1Step
    | ExtendLog2Step
    | Move3Step
    | ReplayStep(replayedUIOp: SM.UIOp)
    | PushSyncStep(ghost id: int)
    | PopSyncStep(ghost id: int)
    | StutterStep

  predicate Crash(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp)
  {
    && uiop.CrashOp?
    && s' == Variables(
      s.s1,
      s.s1,
      s.s1,
      s.j1,
      s.j1,
      s.j1,
      s.j1,
      [],
      map[])
  }

  predicate Move1to2(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp)
  {
    && uiop.NoOp?
    && s' == Variables(
      s.s2,
      s.s2,
      s.s3,
      s.j2,
      s.j2,
      s.j3,
      s.j2,
      s.j_delta,
      SyncReqs2to1(s.outstandingSyncReqs))
  }

  predicate Move2to3(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp)
  {
    && uiop.NoOp?
    && s' == Variables(
      s.s1,
      s.s3,
      s.s3,
      s.j1,
      s.j3,
      s.j3,
      s.j_gamma + s.j_delta,
      [],
      SyncReqs3to2(s.outstandingSyncReqs))
  }

  predicate ExtendLog1(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp)
  {
    && uiop.NoOp?
    && s' == Variables(
      s.s1,
      s.s2,
      s.s3,
      s.j_gamma,
      s.j2,
      s.j3,
      s.j_gamma,
      s.j_delta,
      SyncReqs2to1(s.outstandingSyncReqs))
  }

  predicate ExtendLog2(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp)
  {
    && uiop.NoOp?
    && s' == Variables(
      s.s1,
      s.s2,
      s.s3,
      s.j1,
      s.j2 + s.j_delta,
      s.j3,
      s.j_gamma + s.j_delta,
      [],
      SyncReqs3to2(s.outstandingSyncReqs))
  }

  predicate Move3(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp)
  {
    && SM.Next(k.k, s.s3, s'.s3, uiop)
    && var new_je := JournalEntriesForUIOp(uiop);
    && s.j3 == []
    && s' == Variables(
      s.s1,
      s.s2,
      s'.s3,
      s.j1,
      s.j2,
      s.j3,
      s.j_gamma,
      s.j_delta + new_je,
      s.outstandingSyncReqs)
  }

  predicate Replay(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp, replayedUIOp: SM.UIOp)
  {
    && uiop.NoOp?
    && SM.Next(k.k, s.s3, s'.s3, replayedUIOp)
    && s.j3 == JournalEntriesForUIOp(replayedUIOp) + s'.j3
    && s' == Variables(
      s.s1,
      s.s2,
      s'.s3,
      s.j1,
      s.j2,
      s'.j3,
      s.j_gamma,
      s.j_delta,
      s.outstandingSyncReqs)
  }

  predicate PushSync(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp, id: int)
  {
    && uiop == UI.PushSyncOp(id)
    && id !in s.outstandingSyncReqs
    && s' == Variables(s.s1, s.s2, s.s3, s.j1, s.j2, s.j3, s.j_gamma, s.j_delta, s.outstandingSyncReqs[id := State3])
  }

  predicate PopSync(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp, id: int)
  {
    && uiop == UI.PopSyncOp(id)
    && id in s.outstandingSyncReqs
    && s.outstandingSyncReqs[id] == State1
    && s' == Variables(s.s1, s.s2, s.s3, s.j1, s.j2, s.j3, s.j_gamma, s.j_delta, MapRemove1(s.outstandingSyncReqs, id))
  }

  predicate Stutter(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp)
  {
    && uiop.NoOp?
    && s == s'
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp, step: Step)
  {
    match step {
      case CrashStep => Crash(k, s, s', uiop)
      case Move1to2Step => Move1to2(k, s, s', uiop)
      case Move2to3Step => Move2to3(k, s, s', uiop)
      case ExtendLog1Step => ExtendLog1(k, s, s', uiop)
      case ExtendLog2Step => ExtendLog2(k, s, s', uiop)
      case Move3Step => Move3(k, s, s', uiop)
      case ReplayStep(replayedUIOp) => Replay(k, s, s', uiop, replayedUIOp)
      case PushSyncStep(id) => PushSync(k, s, s', uiop, id)
      case PopSyncStep(id) => PopSync(k, s, s', uiop, id)
      case StutterStep => Stutter(k, s, s', uiop)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp) {
    exists step :: NextStep(k, s, s', uiop, step)
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

  predicate Inv(k: Constants, s: Variables)
  {
    && SM.Inv(k.k, s.s1)
    && SM.Inv(k.k, s.s2)
    && SM.Inv(k.k, s.s3)
    && advances(k.k, s.s1, s.j_gamma, s.s2, s.j2)
    && advances(k.k, s.s2, s.j2 + s.j_delta, s.s3, s.j3)
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
        //assert states[i] == states2[i - |uiops1|];
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

  lemma InitImpliesInv(k: Constants, s: Variables)
  requires Init(k, s)
  ensures Inv(k, s)
  {
    SM.InitImpliesInv(k.k, s.s1);
    path_empty(k.k, s.s1);
  }

  lemma CrashStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UI.Op)
  requires Inv(k, s)
  requires Crash(k, s, s', uiop)
  ensures Inv(k, s')
  {
    path_empty(k.k, s.s1);
  }

  lemma Move1to2StepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UI.Op)
  requires Inv(k, s)
  requires Move1to2(k, s, s', uiop)
  ensures Inv(k, s')
  {
    path_empty(k.k, s.s2);
  }

  lemma Move2to3StepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UI.Op)
  requires Inv(k, s)
  requires Move2to3(k, s, s', uiop)
  ensures Inv(k, s')
  {
    path_empty(k.k, s.s2);
    path_empty(k.k, s.s3);
    assert advances(k.k, s.s1, s.j_gamma, s.s2, s.j2);
    assert advances(k.k, s.s2, s.j2 + s.j_delta, s.s3, s.j3);
    paths_compose(k.k, s.s1,
        SeqSub(s.j_gamma, s.j2),
        s.s2,
        SeqSub(s.j2 + s.j_delta, s.j3),
        s.s3);
    SeqSubAdd(s.j_gamma, s.j2, s.j_delta, s.j3);
    assert SeqSub(s.j_gamma, s.j2) + SeqSub(s.j2 + s.j_delta, s.j3)
        == SeqSub(s.j_gamma + s.j_delta, s.j3);
    assert advances(k.k, s.s1, s.j_gamma + s.j_delta, s.s3, s.j3);
  }

  lemma ExtendLog1StepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UI.Op)
  requires Inv(k, s)
  requires ExtendLog1(k, s, s', uiop)
  ensures Inv(k, s')
  {
  }

  lemma ExtendLog2StepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UI.Op)
  requires Inv(k, s)
  requires ExtendLog2(k, s, s', uiop)
  ensures Inv(k, s')
  {
  }

  lemma Move3StepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UI.Op)
  requires Inv(k, s)
  requires Move3(k, s, s', uiop)
  ensures Inv(k, s')
  {
    SM.NextPreservesInv(k.k, s.s3, s'.s3, uiop);
    var new_je := JournalEntriesForUIOp(uiop);
    path_append(k.k, s.s2, s.j2 + s.j_delta, s.s3, uiop, s'.s3);
    //assert s.j3 == [];
    //assert SeqSub(s.j2 + s.j_delta, s.j3)
    //    == s.j2 + s.j_delta;
    //assert SeqSub(s.j2 + s.j_delta + JournalEntriesForUIOp(uiop), s.j3)
    //    == s.j2 + s.j_delta + JournalEntriesForUIOp(uiop);
  }

  lemma ReplayStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UI.Op, replayedUIOp: SM.UIOp)
  requires Inv(k, s)
  requires Replay(k, s, s', uiop, replayedUIOp)
  ensures Inv(k, s')
  {
    SM.NextPreservesInv(k.k, s.s3, s'.s3, replayedUIOp);
    path_append(k.k, s.s2, SeqSub(s.j2 + s.j_delta, s.j3), s.s3, replayedUIOp, s'.s3);
    // assert SeqSub(s.j2 + s.j_delta, s.j3) + JournalEntriesForUIOp(replayedUIOp)
    //     == SeqSub(s.j2 + s.j_delta, s'.j3);
  }

  lemma PushSyncStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UI.Op, id: int)
  requires Inv(k, s)
  requires PushSync(k, s, s', uiop, id)
  ensures Inv(k, s')
  {
  }

  lemma PopSyncStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UI.Op, id: int)
  requires Inv(k, s)
  requires PopSync(k, s, s', uiop, id)
  ensures Inv(k, s')
  {
  }

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UI.Op, step: Step)
  requires Inv(k, s)
  requires NextStep(k, s, s', uiop, step)
  ensures Inv(k, s')
  {
    match step {
      case CrashStep => CrashStepPreservesInv(k, s, s', uiop);
      case Move1to2Step => Move1to2StepPreservesInv(k, s, s', uiop);
      case Move2to3Step => Move2to3StepPreservesInv(k, s, s', uiop);
      case ExtendLog1Step => ExtendLog1StepPreservesInv(k, s, s', uiop);
      case ExtendLog2Step => ExtendLog2StepPreservesInv(k, s, s', uiop);
      case Move3Step => Move3StepPreservesInv(k, s, s', uiop);
      case ReplayStep(replayedUIOp) => ReplayStepPreservesInv(k, s, s', uiop, replayedUIOp);
      case PushSyncStep(id) => PushSyncStepPreservesInv(k, s, s', uiop, id);
      case PopSyncStep(id) => PopSyncStepPreservesInv(k, s, s', uiop, id);
      case StutterStep => { }
    }
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UI.Op)
  requires Inv(k, s)
  requires Next(k, s, s', uiop)
  ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', uiop, step);
    NextStepPreservesInv(k, s, s', uiop, step);
  }
}
