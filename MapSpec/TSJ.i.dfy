// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "../MapSpec/MapSpec.s.dfy"
include "../MapSpec/UIStateMachine.s.dfy"
include "../lib/Base/Maps.i.dfy"
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

  predicate Init(s: Variables)
  {
    && SM.Init(s.s1)
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

  predicate Crash(s: Variables, s': Variables, uiop: SM.UIOp)
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

  predicate Move1to2(s: Variables, s': Variables, uiop: SM.UIOp)
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

  predicate Move2to3(s: Variables, s': Variables, uiop: SM.UIOp)
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

  predicate ExtendLog1(s: Variables, s': Variables, uiop: SM.UIOp)
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

  predicate ExtendLog2(s: Variables, s': Variables, uiop: SM.UIOp)
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

  predicate Move3(s: Variables, s': Variables, uiop: SM.UIOp)
  {
    && SM.Next(s.s3, s'.s3, uiop)
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

  predicate Replay(s: Variables, s': Variables, uiop: SM.UIOp, replayedUIOp: SM.UIOp)
  {
    && uiop.NoOp?
    && SM.Next(s.s3, s'.s3, replayedUIOp)
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

  predicate PushSync(s: Variables, s': Variables, uiop: SM.UIOp, id: int)
  {
    && uiop == UI.PushSyncOp(id)
    && id !in s.outstandingSyncReqs
    && s' == Variables(s.s1, s.s2, s.s3, s.j1, s.j2, s.j3, s.j_gamma, s.j_delta, s.outstandingSyncReqs[id := State3])
  }

  predicate PopSync(s: Variables, s': Variables, uiop: SM.UIOp, id: int)
  {
    && uiop == UI.PopSyncOp(id)
    && id in s.outstandingSyncReqs
    && s.outstandingSyncReqs[id] == State1
    && s' == Variables(s.s1, s.s2, s.s3, s.j1, s.j2, s.j3, s.j_gamma, s.j_delta, MapRemove1(s.outstandingSyncReqs, id))
  }

  predicate Stutter(s: Variables, s': Variables, uiop: SM.UIOp)
  {
    && uiop.NoOp?
    && s == s'
  }

  predicate NextStep(s: Variables, s': Variables, uiop: SM.UIOp, step: Step)
  {
    match step {
      case CrashStep => Crash(s, s', uiop)
      case Move1to2Step => Move1to2(s, s', uiop)
      case Move2to3Step => Move2to3(s, s', uiop)
      case ExtendLog1Step => ExtendLog1(s, s', uiop)
      case ExtendLog2Step => ExtendLog2(s, s', uiop)
      case Move3Step => Move3(s, s', uiop)
      case ReplayStep(replayedUIOp) => Replay(s, s', uiop, replayedUIOp)
      case PushSyncStep(id) => PushSync(s, s', uiop, id)
      case PopSyncStep(id) => PopSync(s, s', uiop, id)
      case StutterStep => Stutter(s, s', uiop)
    }
  }

  predicate Next(s: Variables, s': Variables, uiop: SM.UIOp) {
    exists step :: NextStep(s, s', uiop, step)
  }

  /// Invariant definition

  predicate IsPath(
      s: SM.Variables,
      uiops: seq<SM.UIOp>,
      s': SM.Variables,
      states: seq<SM.Variables>)
  {
    && |states| == |uiops| + 1
    && states[0] == s
    && states[|states|-1] == s'
    && forall i | 0 <= i < |uiops| ::
        SM.Next(states[i], states[i+1], uiops[i])
  }

  predicate path(
      s: SM.Variables,
      jes: seq<JournalEntry>,
      s': SM.Variables)
  {
    exists states, uiops ::
        && jes == JournalEntriesForUIOps(uiops)
        && IsPath(s, uiops, s', states)
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

  predicate advances(
      s: SM.Variables,
      jes: seq<JournalEntry>, 
      s': SM.Variables,
      jes2: seq<JournalEntry>)
  {
    && IsSuffix(jes, jes2)
    && path(s, SeqSub(jes, jes2), s')
  }

  predicate Inv(s: Variables)
  {
    && SM.Inv(s.s1)
    && SM.Inv(s.s2)
    && SM.Inv(s.s3)
    && advances(s.s1, s.j_gamma, s.s2, s.j2)
    && advances(s.s2, s.j2 + s.j_delta, s.s3, s.j3)
  }

  lemma path_empty(s: SM.Variables)
  ensures path(s, [], s)
  {
    var states := [s];
    var uiops := [];
    assert [] == JournalEntriesForUIOps(uiops);
    assert IsPath(s, uiops, s, states);
  }

  lemma paths_compose(s1: SM.Variables, jes1: seq<JournalEntry>, s2: SM.Variables, jes2: seq<JournalEntry>, s3: SM.Variables)
  requires path(s1, jes1, s2)
  requires path(s2, jes2, s3)
  ensures path(s1, jes1 + jes2, s3)
  {
    var states1, uiops1 :|
        && jes1 == JournalEntriesForUIOps(uiops1)
        && IsPath(s1, uiops1, s2, states1);
    var states2, uiops2 :|
        && jes2 == JournalEntriesForUIOps(uiops2)
        && IsPath(s2, uiops2, s3, states2);

    var states := states1 + states2[1..];
    var uiops := uiops1 + uiops2;

    JournalEntriesForUIOpsAdditive(uiops1, uiops2);
    assert jes1 + jes2 == JournalEntriesForUIOps(uiops);

    forall i | 0 <= i < |uiops|
    ensures SM.Next(states[i], states[i+1], uiops[i]);
    {
      if i < |uiops1| {
        assert states[i] == states1[i];
        assert states[i+1] == states1[i+1];
        assert uiops[i] == uiops1[i];
        assert SM.Next(states1[i], states1[i+1], uiops1[i]);
      } else {
        //assert states[i] == states2[i - |uiops1|];
        assert states[i+1] == states2[i - |uiops1| + 1];
        assert uiops[i] == uiops2[i - |uiops1|];
        assert SM.Next(states2[i - |uiops1|],
            states2[i - |uiops1| + 1], uiops2[i - |uiops1|]);
      }
    }
    assert IsPath(s1, uiops, s3, states);
  }

  lemma path_append(s1: SM.Variables, jes: seq<JournalEntry>, s2: SM.Variables, uiop: SM.UIOp, s3: SM.Variables)
  requires path(s1, jes, s2)
  requires SM.Next(s2, s3, uiop)
  ensures path(s1, jes + JournalEntriesForUIOp(uiop), s3)
  {
    var jes2 := JournalEntriesForUIOp(uiop);
    assert jes2 == JournalEntriesForUIOps([uiop]);
    assert IsPath(s2, [uiop], s3, [s2, s3]);
    assert path(s2, jes2, s3);
    paths_compose(s1, jes, s2, jes2, s3);
  }

  lemma InitImpliesInv(s: Variables)
  requires Init(s)
  ensures Inv(s)
  {
    SM.InitImpliesInv(s.s1);
    path_empty(s.s1);
  }

  lemma CrashStepPreservesInv(s: Variables, s': Variables, uiop: UI.Op)
  requires Inv(s)
  requires Crash(s, s', uiop)
  ensures Inv(s')
  {
    path_empty(s.s1);
  }

  lemma Move1to2StepPreservesInv(s: Variables, s': Variables, uiop: UI.Op)
  requires Inv(s)
  requires Move1to2(s, s', uiop)
  ensures Inv(s')
  {
    path_empty(s.s2);
  }

  lemma Move2to3StepPreservesInv(s: Variables, s': Variables, uiop: UI.Op)
  requires Inv(s)
  requires Move2to3(s, s', uiop)
  ensures Inv(s')
  {
    path_empty(s.s2);
    path_empty(s.s3);
    assert advances(s.s1, s.j_gamma, s.s2, s.j2);
    assert advances(s.s2, s.j2 + s.j_delta, s.s3, s.j3);
    paths_compose(s.s1,
        SeqSub(s.j_gamma, s.j2),
        s.s2,
        SeqSub(s.j2 + s.j_delta, s.j3),
        s.s3);
    SeqSubAdd(s.j_gamma, s.j2, s.j_delta, s.j3);
    assert SeqSub(s.j_gamma, s.j2) + SeqSub(s.j2 + s.j_delta, s.j3)
        == SeqSub(s.j_gamma + s.j_delta, s.j3);
    assert advances(s.s1, s.j_gamma + s.j_delta, s.s3, s.j3);
  }

  lemma ExtendLog1StepPreservesInv(s: Variables, s': Variables, uiop: UI.Op)
  requires Inv(s)
  requires ExtendLog1(s, s', uiop)
  ensures Inv(s')
  {
  }

  lemma ExtendLog2StepPreservesInv(s: Variables, s': Variables, uiop: UI.Op)
  requires Inv(s)
  requires ExtendLog2(s, s', uiop)
  ensures Inv(s')
  {
  }

  lemma Move3StepPreservesInv(s: Variables, s': Variables, uiop: UI.Op)
  requires Inv(s)
  requires Move3(s, s', uiop)
  ensures Inv(s')
  {
    SM.NextPreservesInv(s.s3, s'.s3, uiop);
    var new_je := JournalEntriesForUIOp(uiop);
    path_append(s.s2, s.j2 + s.j_delta, s.s3, uiop, s'.s3);
    //assert s.j3 == [];
    //assert SeqSub(s.j2 + s.j_delta, s.j3)
    //    == s.j2 + s.j_delta;
    //assert SeqSub(s.j2 + s.j_delta + JournalEntriesForUIOp(uiop), s.j3)
    //    == s.j2 + s.j_delta + JournalEntriesForUIOp(uiop);
  }

  lemma ReplayStepPreservesInv(s: Variables, s': Variables, uiop: UI.Op, replayedUIOp: SM.UIOp)
  requires Inv(s)
  requires Replay(s, s', uiop, replayedUIOp)
  ensures Inv(s')
  {
    SM.NextPreservesInv(s.s3, s'.s3, replayedUIOp);
    path_append(s.s2, SeqSub(s.j2 + s.j_delta, s.j3), s.s3, replayedUIOp, s'.s3);
    // assert SeqSub(s.j2 + s.j_delta, s.j3) + JournalEntriesForUIOp(replayedUIOp)
    //     == SeqSub(s.j2 + s.j_delta, s'.j3);
  }

  lemma PushSyncStepPreservesInv(s: Variables, s': Variables, uiop: UI.Op, id: int)
  requires Inv(s)
  requires PushSync(s, s', uiop, id)
  ensures Inv(s')
  {
  }

  lemma PopSyncStepPreservesInv(s: Variables, s': Variables, uiop: UI.Op, id: int)
  requires Inv(s)
  requires PopSync(s, s', uiop, id)
  ensures Inv(s')
  {
  }

  lemma NextStepPreservesInv(s: Variables, s': Variables, uiop: UI.Op, step: Step)
  requires Inv(s)
  requires NextStep(s, s', uiop, step)
  ensures Inv(s')
  {
    match step {
      case CrashStep => CrashStepPreservesInv(s, s', uiop);
      case Move1to2Step => Move1to2StepPreservesInv(s, s', uiop);
      case Move2to3Step => Move2to3StepPreservesInv(s, s', uiop);
      case ExtendLog1Step => ExtendLog1StepPreservesInv(s, s', uiop);
      case ExtendLog2Step => ExtendLog2StepPreservesInv(s, s', uiop);
      case Move3Step => Move3StepPreservesInv(s, s', uiop);
      case ReplayStep(replayedUIOp) => ReplayStepPreservesInv(s, s', uiop, replayedUIOp);
      case PushSyncStep(id) => PushSyncStepPreservesInv(s, s', uiop, id);
      case PopSyncStep(id) => PopSyncStepPreservesInv(s, s', uiop, id);
      case StutterStep => { }
    }
  }

  lemma NextPreservesInv(s: Variables, s': Variables, uiop: UI.Op)
  requires Inv(s)
  requires Next(s, s', uiop)
  ensures Inv(s')
  {
    var step :| NextStep(s, s', uiop, step);
    NextStepPreservesInv(s, s', uiop, step);
  }
}
