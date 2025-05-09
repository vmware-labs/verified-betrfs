// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "TSJMap.i.dfy"
include "ThreeStateVersionedMap.s.dfy"

module TSJMap_Refines_ThreeStateVersionedMap {
  import TSJ = TSJMap
  import TSV = ThreeStateVersionedMap
  import MapSpec
  import opened Journal
  import opened ThreeStateTypes

  import opened Sequences

  function Apply(m: MapSpec.Variables, je: JournalEntry) : MapSpec.Variables
  {
    match je {
      case JournalInsert(key, value) => MapSpec.Variables(m.view[key := value])
      case JournalClone(from, to) => MapSpec.Variables(MapSpec.ApplyCloneView(m.view, MapSpec.CloneMap(from, to)))
    }
  }

  function ApplySeq(m: MapSpec.Variables, jes: seq<JournalEntry>) : MapSpec.Variables
  {
    if jes == [] then
      m
    else
      Apply(ApplySeq(m, DropLast(jes)), Last(jes))
  }

  function ApplyUIOp(m: MapSpec.Variables, uiop: UI.Op) : MapSpec.Variables
  {
    match uiop {
      case PutOp(key, value) => MapSpec.Variables(m.view[key := value])
      case CloneOp(from, to) => MapSpec.Variables(MapSpec.ApplyCloneView(m.view, MapSpec.CloneMap(from, to)))
      case _ => m
    }
  }

  function ApplyUIOpSeq(m: MapSpec.Variables, uiops: seq<UI.Op>) : MapSpec.Variables
  {
    if uiops == [] then
      m
    else
      ApplyUIOp(ApplyUIOpSeq(m, DropLast(uiops)), Last(uiops))
  }

  lemma apply_uiops_path(m: MapSpec.Variables, uiops: seq<UI.Op>, m': MapSpec.Variables, states: seq<MapSpec.Variables>)
  requires TSJ.IsPath(m, uiops, m', states)
  ensures m' == ApplyUIOpSeq(m, uiops)
  {
    if uiops == [] {
    } else {
      calc {
        ApplyUIOpSeq(m, uiops);
        ApplyUIOp(ApplyUIOpSeq(m, DropLast(uiops)), Last(uiops));
        {
          apply_uiops_path(m, DropLast(uiops), states[|states| - 2], DropLast(states));
        }
        ApplyUIOp(states[|states| - 2], Last(uiops));
        {
          assert MapSpec.Next(states[|states| - 2], states[|states| - 1], uiops[|states| - 2]);
        }
        m';
      }
    }
  }

  lemma apply_eq_apply_uiops(m: MapSpec.Variables, uiops: seq<UI.Op>)
  ensures ApplyUIOpSeq(m, uiops) == ApplySeq(m, JournalEntriesForUIOps(uiops))
  {
    if uiops == [] {
    } else {
      apply_eq_apply_uiops(m, DropLast(uiops));
      calc {
        ApplyUIOpSeq(m, uiops);
        ApplyUIOp(ApplyUIOpSeq(m, DropLast(uiops)), Last(uiops));
        ApplyUIOp(ApplySeq(m, JournalEntriesForUIOps(DropLast(uiops))), Last(uiops));
        {
          if Last(uiops).PutOp? || Last(uiops).CloneOp? {
            assert ApplyUIOp(ApplySeq(m, JournalEntriesForUIOps(DropLast(uiops))), Last(uiops))
                == ApplySeq(m, JournalEntriesForUIOps(uiops));
          } else {
            assert JournalEntriesForUIOps(DropLast(uiops))
                == JournalEntriesForUIOps(uiops);
            assert ApplyUIOp(ApplySeq(m, JournalEntriesForUIOps(DropLast(uiops))), Last(uiops))
                == ApplySeq(m, JournalEntriesForUIOps(DropLast(uiops)))
                == ApplySeq(m, JournalEntriesForUIOps(uiops));
          }
        }
        ApplySeq(m, JournalEntriesForUIOps(uiops));
      }
    }
  }

  lemma apply_path(m: MapSpec.Variables, jes: seq<JournalEntry>, m': MapSpec.Variables)
  requires TSJ.path(m, jes, m')
  ensures m' == ApplySeq(m, jes)
  {
    var states, uiops :|
        && jes == JournalEntriesForUIOps(uiops)
        && TSJ.IsPath(m, uiops, m', states);
    apply_eq_apply_uiops(m, uiops);
    apply_uiops_path(m, uiops, m', states);
  }

  lemma ApplySeqAdditive(m: MapSpec.Variables, a: seq<JournalEntry>,
      b: seq<JournalEntry>)
  ensures ApplySeq(m, a+b) == ApplySeq(ApplySeq(m, a), b)
  {
    if b == [] {
      calc {
        ApplySeq(m, a+b);
        { assert a + b == a; }
        ApplySeq(m, a);
        ApplySeq(ApplySeq(m, a), []);
        ApplySeq(ApplySeq(m, a), b);
      }
    } else {
      calc {
        ApplySeq(m, a+b);
        Apply(ApplySeq(m, DropLast(a + b)), Last(a + b));
        {
          assert DropLast(a + b) == a + DropLast(b);
          assert Last(a + b) == Last(b);
        }
        Apply(ApplySeq(m, a + DropLast(b)), Last(b));
        {
          ApplySeqAdditive(m, a, DropLast(b));
        }
        Apply(ApplySeq(ApplySeq(m, a), DropLast(b)), Last(b));
        ApplySeq(ApplySeq(m, a), b);
      }
    }
  }

  lemma ApplySeqPrepend(m: MapSpec.Variables, uiop: UI.Op, m': MapSpec.Variables, j: seq<JournalEntry>)
  requires MapSpec.Next(m, m', uiop)
  ensures ApplySeq(m, JournalEntriesForUIOp(uiop) + j)
       == ApplySeq(m', j)
  {
    assert m' == ApplySeq(m, JournalEntriesForUIOp(uiop));
    ApplySeqAdditive(m, JournalEntriesForUIOp(uiop), j);
  }

  function I(s: TSJ.Variables) : TSV.Variables
  {
    TSV.Variables(
      ApplySeq(s.s1, s.j1),
      ApplySeq(s.s2, s.j2),
      ApplySeq(s.s3, s.j3),
      s.outstandingSyncReqs
    )
  }

  lemma RefinesInit(s: TSJ.Variables)
    requires TSJ.Init(s)
    ensures TSV.Init(I(s))
  {
  }

  lemma RefinesCrash(s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op)
    requires TSJ.Inv(s)
    requires TSJ.Crash(s, s', uiop)
    ensures TSV.Next(I(s), I(s'), uiop)
  {
    assert TSV.NextStep(I(s), I(s'), uiop, TSV.CrashStep);
  }

  lemma RefinesMove1to2(s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op)
    requires TSJ.Inv(s)
    requires TSJ.Move1to2(s, s', uiop)
    ensures TSV.Next(I(s), I(s'), uiop)
  {
    assert TSV.NextStep(I(s), I(s'), uiop, TSV.Move1to2Step);
  }

  lemma RefinesMove2to3(s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op)
    requires TSJ.Inv(s)
    requires TSJ.Move2to3(s, s', uiop)
    ensures TSV.Next(I(s), I(s'), uiop)
  {
    assert TSV.NextStep(I(s), I(s'), uiop, TSV.Move2to3Step);
  }

  lemma RefinesExtendLog1(s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op)
    requires TSJ.Inv(s)
    requires TSJ.ExtendLog1(s, s', uiop)
    ensures TSV.Next(I(s), I(s'), uiop)
  {
    calc {
      ApplySeq(s'.s1, s'.j1);
      ApplySeq(s.s1, s.j_gamma);
      {
        assert s.j_gamma == TSJ.SeqSub(s.j_gamma, s.j2) + s.j2;
      }
      ApplySeq(s.s1, TSJ.SeqSub(s.j_gamma, s.j2) + s.j2);
      {
        ApplySeqAdditive(s.s1, TSJ.SeqSub(s.j_gamma, s.j2), s.j2);
      }
      ApplySeq(ApplySeq(s.s1, TSJ.SeqSub(s.j_gamma, s.j2)), s.j2);
      {
        apply_path(s.s1, TSJ.SeqSub(s.j_gamma, s.j2), s.s2);
      }
      ApplySeq(s.s2, s.j2);
    }
    //assert ApplySeq(s.s2, s.j2)
    //    == ApplySeq(s'.s2, s'.j2);
    //assert I(s').s1 == I(s).s2;
    //assert I(s').s2 == I(s).s2;
    //assert I(s').s3 == I(s).s3;
    //assert I(s').outstandingSyncReqs
    //    == SyncReqs2to1(I(s).outstandingSyncReqs);
    //assert TSV.Move1to2(I(s), I(s'), uiop);
    assert TSV.NextStep(I(s), I(s'), uiop, TSV.Move1to2Step);
  }

  lemma RefinesExtendLog2(s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op)
    requires TSJ.Inv(s)
    requires TSJ.ExtendLog2(s, s', uiop)
    ensures TSV.Next(I(s), I(s'), uiop)
  {
    calc {
      ApplySeq(s.s3, s.j3);
      {
        apply_path(s.s2, TSJ.SeqSub(s.j2 + s.j_delta, s.j3), s.s3);
      }
      ApplySeq(ApplySeq(s.s2, TSJ.SeqSub(s.j2 + s.j_delta, s.j3)), s.j3);
      {
        ApplySeqAdditive(s.s2, TSJ.SeqSub(s.j2 + s.j_delta, s.j3), s.j3);
      }
      ApplySeq(s.s2, TSJ.SeqSub(s.j2 + s.j_delta, s.j3) + s.j3);
      ApplySeq(s.s2, s.j2 + s.j_delta);
      ApplySeq(s'.s2, s'.j2);
    }

    assert I(s').s1 == I(s).s1;
    assert I(s').s2 == I(s).s3;
    assert I(s').s3 == I(s).s3;
    assert I(s').outstandingSyncReqs
        == SyncReqs3to2(I(s).outstandingSyncReqs);

    assert TSV.Move2to3(I(s), I(s'), uiop);
    assert TSV.NextStep(I(s), I(s'), uiop, TSV.Move2to3Step);
  }

  lemma RefinesMove3(s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op)
    requires TSJ.Inv(s)
    requires TSJ.Move3(s, s', uiop)
    ensures TSV.Next(I(s), I(s'), uiop)
  {
    assert TSV.NextStep(I(s), I(s'), uiop, TSV.Move3Step);
  }

  lemma RefinesReplay(s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op, replayedUIOp: UI.Op)
    requires TSJ.Inv(s)
    requires TSJ.Replay(s, s', uiop, replayedUIOp)
    ensures TSV.Next(I(s), I(s'), uiop)
  {
    //assert uiop.NoOp?;
    //assert I(s').s1 == I(s).s1;
    //assert I(s').s2 == I(s).s2;
    calc {
      I(s').s3;
      ApplySeq(s'.s3, s'.j3);
      {
        ApplySeqPrepend(s.s3, replayedUIOp, s'.s3, s'.j3);
      }
      ApplySeq(s.s3, JournalEntriesForUIOp(replayedUIOp) + s'.j3);
      ApplySeq(s.s3, s.j3);
      I(s).s3;
    }
    assert MapSpec.NextStep(I(s).s3, I(s').s3, uiop, MapSpec.StutterStep);
    assert TSV.NextStep(I(s), I(s'), uiop, TSV.Move3Step);
  }

  lemma RefinesPushSync(s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op, id: int)
    requires TSJ.Inv(s)
    requires TSJ.PushSync(s, s', uiop, id)
    ensures TSV.Next(I(s), I(s'), uiop)
  {
    assert TSV.NextStep(I(s), I(s'), uiop,
        TSV.PushSyncStep(id));
  }

  lemma RefinesPopSync(s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op, id: int)
    requires TSJ.Inv(s)
    requires TSJ.PopSync(s, s', uiop, id)
    ensures TSV.Next(I(s), I(s'), uiop)
  {
    assert TSV.NextStep(I(s), I(s'), uiop,
        TSV.PopSyncStep(id));
  }

  lemma RefinesStutter(s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op)
    requires TSJ.Inv(s)
    requires TSJ.Stutter(s, s', uiop)
    ensures TSV.Next(I(s), I(s'), uiop)
  {
    assert MapSpec.NextStep(I(s).s3, I(s').s3, uiop, MapSpec.StutterStep);
    assert TSV.NextStep(I(s), I(s'), uiop, TSV.Move3Step);
  }

  lemma RefinesNextStep(s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op, step: TSJ.Step)
    requires TSJ.Inv(s)
    requires TSJ.NextStep(s, s', uiop, step)
    ensures TSV.Next(I(s), I(s'), uiop)
  {
    match step {
      case CrashStep => RefinesCrash(s, s', uiop);
      case Move1to2Step => RefinesMove1to2(s, s', uiop);
      case Move2to3Step => RefinesMove2to3(s, s', uiop);
      case ExtendLog1Step => RefinesExtendLog1(s, s', uiop);
      case ExtendLog2Step => RefinesExtendLog2(s, s', uiop);
      case Move3Step => RefinesMove3(s, s', uiop);
      case ReplayStep(replayedUIOp) => RefinesReplay(s, s', uiop, replayedUIOp);
      case PushSyncStep(id) => RefinesPushSync(s, s', uiop, id);
      case PopSyncStep(id) => RefinesPopSync(s, s', uiop, id);
      case StutterStep => RefinesStutter(s, s', uiop);
    }
  }

  lemma RefinesNext(s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op)
    requires TSJ.Inv(s)
    requires TSJ.Next(s, s', uiop)
    ensures TSV.Next(I(s), I(s'), uiop)
  {
    var step :| TSJ.NextStep(s, s', uiop, step);
    RefinesNextStep(s, s', uiop, step);
  }
}
