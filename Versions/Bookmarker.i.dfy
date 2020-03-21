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

  ////
  //// Lemmas about applying stuff to states.

  function Apply(m: SM.Variables, je: JournalEntry) : SM.Variables
  {
    SM.Variables(m.view[je.key := je.value])
  }

  function ApplySeq(m: SM.Variables, jes: seq<JournalEntry>) : SM.Variables
  {
    if jes == [] then
      m
    else
      Apply(ApplySeq(m, DropLast(jes)), Last(jes))
  }

  lemma ApplySeqAdditive(m: SM.Variables, a: seq<JournalEntry>,
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

  lemma ApplySeqPrepend(k: SM.Constants, m: SM.Variables, uiop: UI.Op, m': SM.Variables, j: seq<JournalEntry>)
  requires SM.Next(k, m, m', uiop)
  ensures ApplySeq(m, JournalEntriesForUIOp(uiop) + j)
       == ApplySeq(m', j)
  {
    assert m' == ApplySeq(m, JournalEntriesForUIOp(uiop));
    ApplySeqAdditive(m, JournalEntriesForUIOp(uiop), j);
  }

  lemma ApplySeqAppend(k: SM.Constants, m: SM.Variables, j: seq<JournalEntry>, uiop: UI.Op, m': SM.Variables)
  requires SM.Next(k, ApplySeq(m, j), m', uiop)
  ensures ApplySeq(m, j + JournalEntriesForUIOp(uiop)) == m'

  //// Inv definition

  function {:opaque} JournalSlice(s: Variables, a: int, b: int) : (res : seq<JournalEntry>)
  requires 0 <= a - s.jc.startVersion <= |s.jc.journal|
  requires 0 <= b - s.jc.startVersion <= |s.jc.journal|
  requires a <= b
  ensures |res| == b - a
  {
    s.jc.journal[a - s.jc.startVersion .. b - s.jc.startVersion]
  }

  function {:opaque} JournalSuffix(s: Variables, a: int) : (res : seq<JournalEntry>)
  requires 0 <= a - s.jc.startVersion <= |s.jc.journal|
  ensures |res| == |s.jc.journal| - (a - s.jc.startVersion)
  {
    s.jc.journal[a - s.jc.startVersion ..]
  }

  function AllJournalFromPersistentState(s: Variables) : seq<JournalEntry>
  requires 0 <= s.jc.persistentStateIndex - s.jc.startVersion <= |s.jc.journal|
  {
    JournalSuffix(s, s.jc.persistentStateIndex)
  }

  function PersistentJournal(s: Variables) : seq<JournalEntry>
  requires 0 <= s.jc.persistentStateIndex - s.jc.startVersion <= |s.jc.journal|
  {
    JournalSlice(s, s.jc.persistentStateIndex, s.jc.persistentJournalIndex)
  }

  predicate StatesConsistent(
      s: Variables,
      m: SM.Variables,
      m': SM.Variables,
      v1: int, v2: int)
  requires 0 <= v1 - s.jc.startVersion <= |s.jc.journal|
  requires 0 <= v2 - s.jc.startVersion <= |s.jc.journal|
  requires v1 <= v2
  {
    ApplySeq(m, JournalSlice(s, v1, v2)) == m'
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
    && (s.jc.frozenStateIndex.Some? <==> s.tsm.frozenState.Some?)
    && (s.tsm.frozenState.Some? ==>
      s.tsm.ephemeralState.Some?
    )
    && (s.tsm.ephemeralState.Some? ==>
      s.tsm.persistentLoc.Some?
    )
    && s.jc.persistentLoc in s.tsm.disk
    && s.jc.startVersion <= s.jc.persistentStateIndex
    && s.jc.persistentStateIndex <= s.jc.persistentJournalIndex
    && s.jc.persistentStateIndex <= s.jc.ephemeralStateIndex
    && (s.jc.frozenStateIndex.Some? ==> (
      s.jc.persistentStateIndex
        <= s.jc.frozenStateIndex.value
        <= s.jc.ephemeralStateIndex
    ))
    && s.jc.persistentJournalIndex <= s.jc.startVersion + |s.jc.journal|
    && s.jc.ephemeralStateIndex <= s.jc.startVersion + |s.jc.journal|

    && var persistentState := s.tsm.disk[s.jc.persistentLoc];
    && (s.tsm.ephemeralState.Some? ==>
      StatesConsistent(s,
          persistentState, s.tsm.ephemeralState.value,
          s.jc.persistentStateIndex, s.jc.ephemeralStateIndex)
    )
    && (s.jc.frozenStateIndex.Some? ==>
      && StatesConsistent(s,
          persistentState, s.tsm.frozenState.value,
          s.jc.persistentStateIndex, s.jc.frozenStateIndex.value)
      && StatesConsistent(s,
          s.tsm.frozenState.value, s.tsm.ephemeralState.value,
          s.jc.frozenStateIndex.value, s.jc.ephemeralStateIndex)
    )
  }

  lemma InitImpliesInv(k: Constants, s: Variables, s': Variables)
  requires Init(k, s)
  ensures Inv(k, s)
  {
  }

  lemma JournalSliceAppend(k: Constants, s: Variables, s': Variables, vop: VOp, i: int)
  requires Inv(k, s)
  requires JournalChain.Next(k.jc, s.jc, s'.jc, vop)
  requires vop.AdvanceOp?
  requires 0 <= i - s.jc.startVersion <= |s.jc.journal|
  requires 0 <= s.jc.ephemeralStateIndex - s.jc.startVersion <= |s.jc.journal|
  requires i <= s.jc.ephemeralStateIndex
  ensures JournalSlice(s', i, s'.jc.ephemeralStateIndex)
        == JournalSlice(s, i, s.jc.ephemeralStateIndex)
            + JournalEntriesForUIOp(vop.uiop)
  {
    reveal_JournalSlice();
    if JournalChain.AdvanceEphemeral(k.jc, s.jc, s'.jc, vop) {
      assert JournalSlice(s', i, s'.jc.ephemeralStateIndex)
            == JournalSlice(s, i, s.jc.ephemeralStateIndex)
                + JournalEntriesForUIOp(vop.uiop);
    } else if JournalChain.Replay(k.jc, s.jc, s'.jc, vop) {
      assert JournalSlice(s', i, s'.jc.ephemeralStateIndex)
            == JournalSlice(s, i, s.jc.ephemeralStateIndex)
                + JournalEntriesForUIOp(vop.uiop);
    }
  }

  lemma JournalSliceAppendPersistent(k: Constants, s: Variables, s': Variables, vop: VOp)
  requires Inv(k, s)
  requires JournalChain.Next(k.jc, s.jc, s'.jc, vop)
  requires vop.AdvanceOp?
  ensures JournalSlice(s', s'.jc.persistentStateIndex, s'.jc.ephemeralStateIndex)
        == JournalSlice(s, s.jc.persistentStateIndex, s.jc.ephemeralStateIndex)
            + JournalEntriesForUIOp(vop.uiop)
  {
    JournalSliceAppend(k, s, s', vop, s.jc.persistentStateIndex);
  }

  lemma JournalSliceAppendFrozen(k: Constants, s: Variables, s': Variables, vop: VOp)
  requires Inv(k, s)
  requires JournalChain.Next(k.jc, s.jc, s'.jc, vop)
  requires vop.AdvanceOp?
  requires s'.jc.frozenStateIndex.Some?
  ensures JournalSlice(s', s'.jc.frozenStateIndex.value, s'.jc.ephemeralStateIndex)
        == JournalSlice(s, s.jc.frozenStateIndex.value, s.jc.ephemeralStateIndex)
            + JournalEntriesForUIOp(vop.uiop)
  {
    JournalSliceAppend(k, s, s', vop, s.jc.frozenStateIndex.value);
  }
  
  lemma AdvancePreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires NextStep(k, s, s', vop, uiop)
  requires vop.AdvanceOp?
  requires Inv(k, s)
  ensures Inv(k, s')
  {
    var tsm_step :| TriStateMap.NextStep(k.tsm, s.tsm, s'.tsm, vop, tsm_step);
    var jc_step :| JournalChain.NextStep(k.jc, s.jc, s'.jc, vop, jc_step);
    var persistentState := s.tsm.disk[s.jc.persistentLoc];

    ApplySeqAppend(k.tsm.k, persistentState, 
        JournalSlice(s, s.jc.persistentStateIndex, s.jc.ephemeralStateIndex),
        vop.uiop, s'.tsm.ephemeralState.value);
    JournalSliceAppendPersistent(k, s, s', vop);

    if s.jc.frozenStateIndex.Some? {
      assert JournalSlice(s', s'.jc.persistentStateIndex, s'.jc.frozenStateIndex.value)
          == JournalSlice(s, s.jc.persistentStateIndex, s.jc.frozenStateIndex.value)
              by { reveal_JournalSlice(); }

      ApplySeqAppend(k.tsm.k, s.tsm.frozenState.value, 
          JournalSlice(s, s.jc.frozenStateIndex.value, s.jc.ephemeralStateIndex),
          vop.uiop, s'.tsm.ephemeralState.value);
      JournalSliceAppendFrozen(k, s, s', vop);
    }

    if JournalChain.AdvanceEphemeral(k.jc, s.jc, s'.jc, vop) {
      assert Inv(k, s');
    } else if JournalChain.Replay(k.jc, s.jc, s'.jc, vop) {
      assert Inv(k, s');
    }
  }

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires NextStep(k, s, s', vop, uiop)
  requires Inv(k, s)
  ensures Inv(k, s')
  {
    reveal_JournalSlice();

    var tsm_step :| TriStateMap.NextStep(k.tsm, s.tsm, s'.tsm, vop, tsm_step);
    var jc_step :| JournalChain.NextStep(k.jc, s.jc, s'.jc, vop, jc_step);

    var persistentState := s.tsm.disk[s.jc.persistentLoc];

    match vop {
      case SendPersistentLocOp(loc) => { }
      case AdvanceOp(_, _) => {
        AdvancePreservesInv(k, s, s', vop, uiop);
      }
      case CrashOp => {
        assert JournalChain.Crash(k.jc, s.jc, s'.jc, vop);
        assert TriStateMap.Crash(k.tsm, s.tsm, s'.tsm, vop);
      }
      case FreezeOp => { }
      case TristateInternalOp => { }
      case JournalInternalOp => {
        assert s.tsm == s'.tsm;
        if JournalChain.AdvancePersistent(k.jc, s.jc, s'.jc, vop) {
          assert Inv(k, s');
        }
        else if JournalChain.CleanUpStep(k.jc, s.jc, s'.jc, vop) {
          assert Inv(k, s');
        }
        else {
          assert s.jc == s'.jc;
        }
      }
      case SendFrozenLocOp(loc) => { }
      case ForgetOldOp => {
        assert JournalChain.ForgetOld(k.jc, s.jc, s'.jc, vop);
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
