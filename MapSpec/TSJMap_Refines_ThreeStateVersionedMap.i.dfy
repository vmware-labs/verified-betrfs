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
    MapSpec.Variables(m.view[je.key := je.value])
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
    if uiop.PutOp? then
      MapSpec.Variables(m.view[uiop.key := uiop.value])
    else
      m
  }

  function ApplyUIOpSeq(m: MapSpec.Variables, uiops: seq<UI.Op>) : MapSpec.Variables
  {
    if uiops == [] then
      m
    else
      ApplyUIOp(ApplyUIOpSeq(m, DropLast(uiops)), Last(uiops))
  }

  lemma apply_uiops_path(k: MapSpec.Constants, m: MapSpec.Variables, uiops: seq<UI.Op>, m': MapSpec.Variables, states: seq<MapSpec.Variables>)
  requires TSJ.IsPath(k, m, uiops, m', states)
  ensures m' == ApplyUIOpSeq(m, uiops)
  {
    if uiops == [] {
    } else {
      calc {
        ApplyUIOpSeq(m, uiops);
        ApplyUIOp(ApplyUIOpSeq(m, DropLast(uiops)), Last(uiops));
        {
          apply_uiops_path(k, m, DropLast(uiops), states[|states| - 2], DropLast(states));
        }
        ApplyUIOp(states[|states| - 2], Last(uiops));
        {
          assert MapSpec.Next(k, states[|states| - 2], states[|states| - 1], uiops[|states| - 2]);
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
          if Last(uiops).PutOp? {
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

  lemma apply_path(k: MapSpec.Constants, m: MapSpec.Variables, jes: seq<JournalEntry>, m': MapSpec.Variables)
  requires TSJ.path(k, m, jes, m')
  ensures m' == ApplySeq(m, jes)
  {
    var states, uiops :|
        && jes == JournalEntriesForUIOps(uiops)
        && TSJ.IsPath(k, m, uiops, m', states);
    apply_eq_apply_uiops(m, uiops);
    apply_uiops_path(k, m, uiops, m', states);
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

  lemma ApplySeqPrepend(k: MapSpec.Constants, m: MapSpec.Variables, uiop: UI.Op, m': MapSpec.Variables, j: seq<JournalEntry>)
  requires MapSpec.Next(k, m, m', uiop)
  ensures ApplySeq(m, JournalEntriesForUIOp(uiop) + j)
       == ApplySeq(m', j)
  {
    assert m' == ApplySeq(m, JournalEntriesForUIOp(uiop));
    ApplySeqAdditive(m, JournalEntriesForUIOp(uiop), j);
  }

  function Ik(k: TSJ.Constants) : TSV.Constants
  {
    TSV.Constants(k.k)
  }

  function I(k: TSJ.Constants, s: TSJ.Variables) : TSV.Variables
  {
    TSV.Variables(
      ApplySeq(s.s1, s.j1),
      ApplySeq(s.s2, s.j2),
      ApplySeq(s.s3, s.j3),
      s.outstandingSyncReqs
    )
  }

  lemma RefinesInit(k: TSJ.Constants, s: TSJ.Variables)
    requires TSJ.Init(k, s)
    ensures TSV.Init(Ik(k), I(k, s))
  {
  }

  lemma RefinesCrash(k: TSJ.Constants, s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op)
    requires TSJ.Inv(k, s)
    requires TSJ.Crash(k, s, s', uiop)
    ensures TSV.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSV.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSV.CrashStep);
  }

  lemma RefinesMove1to2(k: TSJ.Constants, s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op)
    requires TSJ.Inv(k, s)
    requires TSJ.Move1to2(k, s, s', uiop)
    ensures TSV.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSV.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSV.Move1to2Step);
  }

  lemma RefinesMove2to3(k: TSJ.Constants, s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op)
    requires TSJ.Inv(k, s)
    requires TSJ.Move2to3(k, s, s', uiop)
    ensures TSV.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSV.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSV.Move2to3Step);
  }

  lemma RefinesExtendLog1(k: TSJ.Constants, s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op)
    requires TSJ.Inv(k, s)
    requires TSJ.ExtendLog1(k, s, s', uiop)
    ensures TSV.Next(Ik(k), I(k, s), I(k, s'), uiop)
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
        apply_path(k.k, s.s1, TSJ.SeqSub(s.j_gamma, s.j2), s.s2);
      }
      ApplySeq(s.s2, s.j2);
    }
    //assert ApplySeq(s.s2, s.j2)
    //    == ApplySeq(s'.s2, s'.j2);
    //assert I(k, s').s1 == I(k, s).s2;
    //assert I(k, s').s2 == I(k, s).s2;
    //assert I(k, s').s3 == I(k, s).s3;
    //assert I(k, s').outstandingSyncReqs
    //    == SyncReqs2to1(I(k, s).outstandingSyncReqs);
    //assert TSV.Move1to2(Ik(k), I(k, s), I(k, s'), uiop);
    assert TSV.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSV.Move1to2Step);
  }

  lemma RefinesExtendLog2(k: TSJ.Constants, s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op)
    requires TSJ.Inv(k, s)
    requires TSJ.ExtendLog2(k, s, s', uiop)
    ensures TSV.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    calc {
      ApplySeq(s.s3, s.j3);
      {
        apply_path(k.k, s.s2, TSJ.SeqSub(s.j2 + s.j_delta, s.j3), s.s3);
      }
      ApplySeq(ApplySeq(s.s2, TSJ.SeqSub(s.j2 + s.j_delta, s.j3)), s.j3);
      {
        ApplySeqAdditive(s.s2, TSJ.SeqSub(s.j2 + s.j_delta, s.j3), s.j3);
      }
      ApplySeq(s.s2, TSJ.SeqSub(s.j2 + s.j_delta, s.j3) + s.j3);
      ApplySeq(s.s2, s.j2 + s.j_delta);
      ApplySeq(s'.s2, s'.j2);
    }

    assert I(k, s').s1 == I(k, s).s1;
    assert I(k, s').s2 == I(k, s).s3;
    assert I(k, s').s3 == I(k, s).s3;
    assert I(k, s').outstandingSyncReqs
        == SyncReqs3to2(I(k, s).outstandingSyncReqs);

    assert TSV.Move2to3(Ik(k), I(k, s), I(k, s'), uiop);
    assert TSV.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSV.Move2to3Step);
  }

  lemma RefinesMove3(k: TSJ.Constants, s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op)
    requires TSJ.Inv(k, s)
    requires TSJ.Move3(k, s, s', uiop)
    ensures TSV.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSV.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSV.Move3Step);
  }

  lemma RefinesReplay(k: TSJ.Constants, s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op, replayedUIOp: UI.Op)
    requires TSJ.Inv(k, s)
    requires TSJ.Replay(k, s, s', uiop, replayedUIOp)
    ensures TSV.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    //assert uiop.NoOp?;
    //assert I(k, s').s1 == I(k, s).s1;
    //assert I(k, s').s2 == I(k, s).s2;
    calc {
      I(k, s').s3;
      ApplySeq(s'.s3, s'.j3);
      {
        ApplySeqPrepend(k.k, s.s3, replayedUIOp, s'.s3, s'.j3);
      }
      ApplySeq(s.s3, JournalEntriesForUIOp(replayedUIOp) + s'.j3);
      ApplySeq(s.s3, s.j3);
      I(k, s).s3;
    }
    assert MapSpec.NextStep(Ik(k).k, I(k, s).s3, I(k, s').s3, uiop, MapSpec.StutterStep);
    assert TSV.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSV.Move3Step);
  }

  lemma RefinesPushSync(k: TSJ.Constants, s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op, id: int)
    requires TSJ.Inv(k, s)
    requires TSJ.PushSync(k, s, s', uiop, id)
    ensures TSV.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSV.NextStep(Ik(k), I(k, s), I(k, s'), uiop,
        TSV.PushSyncStep(id));
  }

  lemma RefinesPopSync(k: TSJ.Constants, s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op, id: int)
    requires TSJ.Inv(k, s)
    requires TSJ.PopSync(k, s, s', uiop, id)
    ensures TSV.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSV.NextStep(Ik(k), I(k, s), I(k, s'), uiop,
        TSV.PopSyncStep(id));
  }

  lemma RefinesStutter(k: TSJ.Constants, s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op)
    requires TSJ.Inv(k, s)
    requires TSJ.Stutter(k, s, s', uiop)
    ensures TSV.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert MapSpec.NextStep(Ik(k).k, I(k, s).s3, I(k, s').s3, uiop, MapSpec.StutterStep);
    assert TSV.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSV.Move3Step);
  }

  lemma RefinesNextStep(k: TSJ.Constants, s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op, step: TSJ.Step)
    requires TSJ.Inv(k, s)
    requires TSJ.NextStep(k, s, s', uiop, step)
    ensures TSV.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    match step {
      case CrashStep => RefinesCrash(k, s, s', uiop);
      case Move1to2Step => RefinesMove1to2(k, s, s', uiop);
      case Move2to3Step => RefinesMove2to3(k, s, s', uiop);
      case ExtendLog1Step => RefinesExtendLog1(k, s, s', uiop);
      case ExtendLog2Step => RefinesExtendLog2(k, s, s', uiop);
      case Move3Step => RefinesMove3(k, s, s', uiop);
      case ReplayStep(replayedUIOp) => RefinesReplay(k, s, s', uiop, replayedUIOp);
      case PushSyncStep(id) => RefinesPushSync(k, s, s', uiop, id);
      case PopSyncStep(id) => RefinesPopSync(k, s, s', uiop, id);
      case StutterStep => RefinesStutter(k, s, s', uiop);
    }
  }

  lemma RefinesNext(k: TSJ.Constants, s: TSJ.Variables, s':TSJ.Variables, uiop: UI.Op)
    requires TSJ.Inv(k, s)
    requires TSJ.Next(k, s, s', uiop)
    ensures TSV.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    var step :| TSJ.NextStep(k, s, s', uiop, step);
    RefinesNextStep(k, s, s', uiop, step);
  }
}
