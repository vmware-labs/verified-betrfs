include "../ByteBlockCacheSystem/JournalBytes.i.dfy"
include "../BlockCacheSystem/DiskLayout.i.dfy"
include "JournalistMarshallingModel.i.dfy"

module JournalistModel {
  import opened DiskLayout
  import opened NativeTypes
  import opened Options
  import opened Sequences

  import opened JournalRanges`Internal
  import opened JournalBytes
  import opened Journal
  import opened JournalistMarshallingModel

  datatype JournalInfo = JournalInfo(
    inMemoryJournalFrozen: seq<JournalEntry>,
    inMemoryJournal: seq<JournalEntry>,
    replayJournal: seq<JournalEntry>,

    journalFront: Option<JournalRange>,
    journalBack: Option<JournalRange>,

    ghost writtenJournalLen: int
  )

  datatype JournalistModel = JournalistModel(
    journalEntries: seq<JournalEntry>,
    start: uint64,
    len1: uint64,
    len2: uint64,

    replayJournal: seq<JournalEntry>,
    replayIdx: uint64,

    journalFront: Option<seq<JournalBlock>>,
    journalBack: Option<seq<JournalBlock>>,
    
    // number of blocks already written on disk:
    writtenJournalBlocks: uint64,
    // number of *blocks* of inMemoryJournalFrozen:
    frozenJournalBlocks: uint64,
    // number of *bytes* of inMemoryJournal:
    inMemoryWeight: uint64
  )

  function method MaxPossibleEntries() : uint64 { 32*1048576 }

  function method basic_mod(x: uint64, len: uint64) : uint64
  requires len <= 2 * MaxPossibleEntries()
  {
    if x >= len then x - len else x
  }

  predicate CorrectJournalBlockSizes(jr: JournalRange)
  {
    && |jr| <= NumJournalBlocks() as int
    && (forall i | 0 <= i < |jr| :: |jr[i]| == 4064)
  }

  predicate WF(jm: JournalistModel)
  {
    && 1 <= |jm.journalEntries| <= 2 * MaxPossibleEntries() as int
    && 0 <= jm.start < |jm.journalEntries| as uint64
    && 0 <= jm.len1 <= |jm.journalEntries| as uint64
    && 0 <= jm.len2 <= |jm.journalEntries| as uint64
    && 0 <= jm.len1 + jm.len2 <= |jm.journalEntries| as uint64
    && 0 <= jm.replayIdx as int <= |jm.replayJournal| <= MaxPossibleEntries() as int
    && (jm.journalFront.Some? ==>
        CorrectJournalBlockSizes(jm.journalFront.value))
    && (jm.journalBack.Some? ==>
        CorrectJournalBlockSizes(jm.journalBack.value))
    && 0 <= jm.writtenJournalBlocks <= NumJournalBlocks()
    && 0 <= jm.frozenJournalBlocks <= NumJournalBlocks()
    && 0 <= jm.inMemoryWeight <= NumJournalBlocks() * 4096
  }

  /*function IJournalRead(j: Option<seq<byte>>) : Option<JournalRange>
  requires j.Some? ==> JournalRangeOfByteSeq(j.value).Some?
  {
    if j.Some? then JournalRangeOfByteSeq(j.value) else None
  }*/

  function start(jm: JournalistModel) : uint64
  {
    jm.start
  }

  function mid(jm: JournalistModel, len: uint64) : uint64
  requires len <= 2 * MaxPossibleEntries()
  requires jm.start < len
  requires jm.len1 <= len
  {
    basic_mod(jm.start + jm.len1, len)
  }

  function end(jm: JournalistModel, len: uint64) : uint64
  requires len <= 2 * MaxPossibleEntries()
  requires jm.start < len
  requires jm.len1 <= len
  requires jm.len2 <= len
  {
    basic_mod(jm.start + jm.len1 + jm.len2, len)
  }

  function InMemoryJournalFrozen(jm: JournalistModel) : seq<JournalEntry>
  requires WF(jm)
  {
    cyclicSlice(jm.journalEntries, start(jm), jm.len1)
  }

  function InMemoryJournal(jm: JournalistModel) : seq<JournalEntry>
  requires WF(jm)
  {
    cyclicSlice(jm.journalEntries,
      mid(jm, |jm.journalEntries| as uint64),
      jm.len2)
  }

  function ReplayJournal(jm: JournalistModel) : seq<JournalEntry>
  requires 0 <= jm.replayIdx as int <= |jm.replayJournal|
  {
    jm.replayJournal[jm.replayIdx..]
  }

  function JournalFrontRead(jm: JournalistModel) : Option<JournalRange>
  requires WF(jm)
  {
    jm.journalFront
  }

  function JournalBackRead(jm: JournalistModel) : Option<JournalRange>
  requires WF(jm)
  {
    jm.journalBack
  }

  function WrittenJournalLen(jm: JournalistModel) : int
  {
    jm.writtenJournalBlocks as int
  }

  function Iprivate(jm: JournalistModel) : JournalInfo
  requires WF(jm)
  {
    JournalInfo(
      InMemoryJournalFrozen(jm),
      InMemoryJournal(jm),
      ReplayJournal(jm),
      JournalFrontRead(jm),
      JournalBackRead(jm),
      WrittenJournalLen(jm)
    )
  }

  protected function I(jm: JournalistModel) : JournalInfo
  requires WF(jm)
  {
    Iprivate(jm)
  }

  lemma reveal_I(jm: JournalistModel)
  requires WF(jm)
  ensures I(jm) == Iprivate(jm)
  {
  }

  predicate Inv(jm: JournalistModel)
  {
    && WF(jm)
    && (jm.writtenJournalBlocks + jm.frozenJournalBlocks) * 4064 +
        jm.inMemoryWeight <= 4064 * NumJournalBlocks()
    && WeightJournalEntries(InMemoryJournalFrozen(jm)) <= jm.frozenJournalBlocks as int * 4064
    && WeightJournalEntries(InMemoryJournal(jm)) == jm.inMemoryWeight as int
  }

  //// Journalist operations

  function {:opaque} JournalistConstructor() : (jm : JournalistModel)
  ensures Inv(jm)
  ensures I(jm).inMemoryJournalFrozen == []
  ensures I(jm).inMemoryJournal == []
  ensures I(jm).replayJournal == []
  ensures I(jm).journalFront == None
  ensures I(jm).journalBack == None
  ensures I(jm).writtenJournalLen == 0
  {
    reveal_cyclicSlice();
    reveal_WeightJournalEntries();
    JournalistModel(
        fill(4096, JournalInsert([], [])), // fill with dummies
        0, 0, 0, [], 0, None, None, 0, 0, 0)
  }

  function {:opaque} hasFrozenJournal(jm: JournalistModel) : (b: bool)
  requires Inv(jm)
  ensures b == (I(jm).inMemoryJournalFrozen != [])
  {
    jm.len1 != 0
  }

  function {:opaque} hasInMemoryJournal(jm: JournalistModel) : (b: bool)
  requires Inv(jm)
  ensures b == (I(jm).inMemoryJournal != [])
  {
    jm.len2 != 0
  }

  function {:opaque} packageFrozenJournal(jm: JournalistModel)
      : (res : (JournalistModel, seq<byte>))
  requires Inv(jm)
  requires I(jm).inMemoryJournalFrozen != []
  ensures var (jm', s) := res;
    && Inv(jm')
    && JournalRangeOfByteSeq(s).Some?
    && parseJournalRange(JournalRangeOfByteSeq(s).value) == Some(I(jm).inMemoryJournalFrozen)
    && I(jm') == I(jm)
          .(inMemoryJournalFrozen := [])
          .(writtenJournalLen := I(jm).writtenJournalLen
                + |JournalRangeOfByteSeq(s).value|)
    && |JournalRangeOfByteSeq(s).value| + I(jm).writtenJournalLen as int
        <= NumJournalBlocks() as int
  {
    reveal_WeightJournalEntries();
    var s := marshallJournalEntries(jm.journalEntries, jm.start, jm.len1, jm.frozenJournalBlocks);
    var jm' := jm.(start := basic_mod(jm.start + jm.len1, |jm.journalEntries| as uint64))
                 .(len1 := 0)
                 .(frozenJournalBlocks := 0)
                 .(writtenJournalBlocks := jm.writtenJournalBlocks + jm.frozenJournalBlocks);
    (jm', s)
  }

  function {:opaque} packageInMemoryJournal(jm: JournalistModel)
      : (res : (JournalistModel, seq<byte>))
  requires Inv(jm)
  requires I(jm).inMemoryJournalFrozen == []
  requires I(jm).inMemoryJournal != []
  ensures var (jm', s) := res;
    && Inv(jm')
    && JournalRangeOfByteSeq(s).Some?
    && parseJournalRange(JournalRangeOfByteSeq(s).value) == Some(I(jm).inMemoryJournal)
    && I(jm') == I(jm)
          .(inMemoryJournal := [])
          .(writtenJournalLen := I(jm).writtenJournalLen
                + |JournalRangeOfByteSeq(s).value|)
    && |JournalRangeOfByteSeq(s).value| + I(jm).writtenJournalLen as int
        <= NumJournalBlocks() as int
  {
    reveal_WeightJournalEntries();
    var numBlocks := (jm.inMemoryWeight + 4064 - 1) / 4064;
    var s := marshallJournalEntries(jm.journalEntries, jm.start, jm.len2, numBlocks);
    var jm' := jm.(start := 0)
                 .(len2 := 0)
                 .(inMemoryWeight := 0)
                 .(writtenJournalBlocks := jm.writtenJournalBlocks + numBlocks);
    (jm', s)
  }

  function getWrittenJournalLen(jm: JournalistModel)
      : (len : uint64)
  requires Inv(jm)
  ensures len as int == I(jm).writtenJournalLen
  {
    jm.writtenJournalBlocks    
  }

  function setWrittenJournalLen(jm: JournalistModel, len: uint64)
      : (jm' : JournalistModel)
  requires Inv(jm)
  requires I(jm).inMemoryJournal == []
  requires I(jm).inMemoryJournalFrozen == []
  requires 0 <= len <= NumJournalBlocks()
  ensures Inv(jm')
  ensures I(jm') == I(jm).(writtenJournalLen := len as int)
  {
    reveal_WeightJournalEntries();
    jm.(writtenJournalBlocks := len)
      .(frozenJournalBlocks := 0)
  }

  function updateWrittenJournalLen(jm: JournalistModel, len: uint64)
      : (jm' : JournalistModel)
  requires Inv(jm)
  requires len as int <= I(jm).writtenJournalLen
  ensures Inv(jm')
  ensures I(jm') == I(jm).(writtenJournalLen := len as int)
  {
    reveal_WeightJournalEntries();
    jm.(writtenJournalBlocks := len)
  }

  /*lemma roundUpOkay(a: int, b: int)
  requires a <= 4064 * b
  ensures ((a + 4064 - 1) / 4064) * 4064 <= 4064 * b
  {
  }*/

  function {:opaque} freeze(jm: JournalistModel) : (jm' : JournalistModel)
  requires Inv(jm)
  ensures
    && Inv(jm')
    && I(jm') == I(jm)
          .(inMemoryJournal := [])
          .(inMemoryJournalFrozen :=
              I(jm).inMemoryJournalFrozen + I(jm).inMemoryJournal)
  {
    var jm' := jm.(len1 := jm.len1 + jm.len2)
      .(len2 := 0)
      .(frozenJournalBlocks := jm.frozenJournalBlocks + (jm.inMemoryWeight + 4064 - 1) / 4064)
      .(inMemoryWeight := 0);

    reveal_WeightJournalEntries();
    assert I(jm').inMemoryJournalFrozen ==
        I(jm).inMemoryJournalFrozen + I(jm).inMemoryJournal
      by { reveal_cyclicSlice(); }

    WeightJournalEntriesSum(I(jm).inMemoryJournalFrozen, I(jm).inMemoryJournal);
    //roundUpOkay(jm.inMemoryWeight as int,
    //  NumJournalBlocks() as int - (jm.writtenJournalBlocks + jm.frozenJournalBlocks) as int);

    jm'
  }

  predicate {:opaque} canAppend(jm: JournalistModel, je: JournalEntry)
  requires Inv(jm)
  {
    4064 * (jm.writtenJournalBlocks + jm.frozenJournalBlocks)
      + jm.inMemoryWeight
      + WeightJournalEntry(je) as uint64
      + (if jm.len2 == 0 then 8 else 0)
        <= 4064 * NumJournalBlocks()
  }

  lemma lemma_weight_append(a: seq<JournalEntry>, je: JournalEntry)
  ensures |a| == 0 ==> WeightJournalEntries(a + [je])
      == WeightJournalEntries(a) + WeightJournalEntry(je) + 8
  ensures |a| > 0 ==> WeightJournalEntries(a + [je])
      == WeightJournalEntries(a) + WeightJournalEntry(je)
  {
    assert DropLast(a + [je]) == a;
    assert Last(a + [je]) == je;
    reveal_WeightJournalEntries();
    if |a| == 0 {
      assert WeightJournalEntries(a + [je])
          == 8 + SumJournalEntries(a) + WeightJournalEntry(je)
          == 8 + SumJournalEntries([]) + WeightJournalEntry(je)
          == 8 + WeightJournalEntry(je);
      assert WeightJournalEntries(a) == 0;
    }
  }

  function {:opaque} append(jm: JournalistModel, je: JournalEntry) : (jm' : JournalistModel)
  requires Inv(jm)
  requires canAppend(jm, je)
  ensures
    && Inv(jm')
    && I(jm') == I(jm).(inMemoryJournal := I(jm).inMemoryJournal + [je])
  {
    lenTimes8LeWeight(InMemoryJournal(jm));
    lenTimes8LeWeight(InMemoryJournalFrozen(jm));

    var (start', journalEntries') := 
      if jm.len1 + jm.len2 < |jm.journalEntries| as uint64 then (
        var idx := basic_mod(jm.start + jm.len1 + jm.len2, |jm.journalEntries| as uint64);
        (jm.start, jm.journalEntries[idx as int := je])
      ) else (
        var newLen: uint64 := |jm.journalEntries| as uint64 * 2;
        (0, jm.journalEntries[jm.start..]
            + jm.journalEntries[..jm.start]
            + [je]
            + fill((newLen as int - |jm.journalEntries| - 1),
                JournalInsert([], [])))
      );

    var jm' := jm
      .(journalEntries := journalEntries')
      .(start := start')
      .(len2 := jm.len2 + 1)
      .(inMemoryWeight := jm.inMemoryWeight + WeightJournalEntry(je) as uint64 + (if jm.len2 == 0 then 8 else 0));

    assert InMemoryJournal(jm')
        == InMemoryJournal(jm) + [je] by { reveal_cyclicSlice(); }
    assert InMemoryJournalFrozen(jm')
        == InMemoryJournalFrozen(jm) by { reveal_cyclicSlice(); }
    lemma_weight_append(InMemoryJournal(jm), je);
    reveal_canAppend();

    jm'
  }

  function {:opaque} isReplayEmpty(jm: JournalistModel) : (b: bool)
  requires Inv(jm)
  ensures b == (I(jm).replayJournal == [])
  {
    jm.replayIdx == |jm.replayJournal| as uint64
  }

  function {:opaque} replayJournalTop(jm: JournalistModel) : (je: JournalEntry)
  requires Inv(jm)
  requires I(jm).replayJournal != []
  ensures je == I(jm).replayJournal[0]
  {
    jm.replayJournal[jm.replayIdx]
  }

  function {:opaque} replayJournalPop(jm: JournalistModel) : (jm': JournalistModel)
  requires Inv(jm)
  requires I(jm).replayJournal != []
  ensures Inv(jm')
  ensures I(jm') == I(jm).(replayJournal := I(jm').replayJournal)
  ensures I(jm).replayJournal
      == [replayJournalTop(jm)] + I(jm').replayJournal
  {
    jm.(replayIdx := jm.replayIdx + 1)
  }

  function {:opaque} setFront(jm: JournalistModel, jr: JournalRange)
    : (jm': JournalistModel)
  requires Inv(jm)
  requires forall i | 0 <= i < |jr| :: |jr[i]| == 4064
  requires |jr| <= NumJournalBlocks() as int
  ensures Inv(jm')
  ensures I(jm') == I(jm).(journalFront := Some(jr))
  {
    jm.(journalFront := Some(jr))
  }

  function {:opaque} setBack(jm: JournalistModel, jr: JournalRange)
    : (jm': JournalistModel)
  requires Inv(jm)
  requires forall i | 0 <= i < |jr| :: |jr[i]| == 4064
  requires |jr| <= NumJournalBlocks() as int
  ensures Inv(jm')
  ensures I(jm') == I(jm).(journalBack := Some(jr))
  {
    jm.(journalBack := Some(jr))
  }

  function {:opaque} parseJournals(jm: JournalistModel)
    : (res : (JournalistModel, bool))
  requires Inv(jm)
  ensures var (jm', success) := res;
    && Inv(jm')
    && (!success ==> I(jm) == I(jm'))
    && (success ==>
      var fullRange :=
        (if I(jm).journalFront.Some? then I(jm).journalFront.value
            else []) +
        (if I(jm).journalBack.Some? then I(jm).journalBack.value
            else []);
      && parseJournalRange(fullRange).Some?
      && I(jm') == I(jm)
          .(journalFront := None)
          .(journalBack := None)
          .(replayJournal := parseJournalRange(fullRange).value)
    )
  {
    var fullRange :=
      (if jm.journalFront.Some? then jm.journalFront.value else []) +
      (if jm.journalBack.Some? then jm.journalBack.value else []);
    var p := parseJournalRange(fullRange);
    if p.Some? && |p.value| <= MaxPossibleEntries() as int then
      var jm' := jm
        .(journalFront := None)
        .(journalBack := None)
        .(replayJournal := p.value)
        .(replayIdx := 0);
      (jm', true)
    else
      (jm, false)
  }

  function {:opaque} hasFront(jm: JournalistModel)
    : (b : bool)
  requires Inv(jm)
  ensures b == I(jm).journalFront.Some?
  {
    jm.journalFront.Some?
  }

  function {:opaque} hasBack(jm: JournalistModel)
    : (b : bool)
  requires Inv(jm)
  ensures b == I(jm).journalBack.Some?
  {
    jm.journalBack.Some?
  }
}
