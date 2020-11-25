include "../lib/Lang/System/NativeArrays.s.dfy"
include "JournalistMarshallingImpl.i.dfy"
include "JournalistParsingImpl.i.dfy"
include "JournalistMarshallingModel.i.dfy"

module JournalistImpl {
  import opened DiskLayout
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import NativeArrays

  import opened JournalRanges`Internal
  import opened JournalBytes
  import opened Journal
  import opened JournalistMarshallingModel
  import opened JournalistMarshallingImpl
  import JournalistParsingImpl

  datatype JournalInfo = JournalInfo(
    inMemoryJournalFrozen: seq<JournalEntry>,
    inMemoryJournal: seq<JournalEntry>,
    replayJournal: seq<JournalEntry>,

    journalFront: Option<JournalRange>,
    journalBack: Option<JournalRange>,

    ghost writtenJournalLen: int
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

  linear datatype Journalist = Journalist(
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
    inMemoryWeight: uint64)
  {

    predicate WF()
    {
      && 1 <= |journalEntries| <= 2 * MaxPossibleEntries() as int
      && 0 <= start < |journalEntries| as uint64
      && 0 <= len1 <= |journalEntries| as uint64
      && 0 <= len2 <= |journalEntries| as uint64
      && 0 <= len1 + len2 <= |journalEntries| as uint64
      && 0 <= replayIdx as int <= |replayJournal| <= MaxPossibleEntries() as int
      && (journalFront.Some? ==>
          CorrectJournalBlockSizes(journalFront.value))
      && (journalBack.Some? ==>
          CorrectJournalBlockSizes(journalBack.value))
      && 0 <= writtenJournalBlocks <= NumJournalBlocks()
      && 0 <= frozenJournalBlocks <= NumJournalBlocks()
      && 0 <= inMemoryWeight <= NumJournalBlocks() * 4096
    }

    predicate Inv()
    {
      && WF()
      && (writtenJournalBlocks + frozenJournalBlocks) * 4064 +
          inMemoryWeight <= 4064 * NumJournalBlocks()
      && WeightJournalEntries(InMemoryJournalFrozen()) <= frozenJournalBlocks as int * 4064
      && WeightJournalEntries(InMemoryJournal()) == inMemoryWeight as int
    }

    function mid(len: uint64) : uint64
    requires len <= 2 * MaxPossibleEntries()
    requires start < len
    requires len1 <= len
    {
      basic_mod(start + len1, len)
    }

    function end(len: uint64) : uint64
    requires len <= 2 * MaxPossibleEntries()
    requires start < len
    requires len1 <= len
    requires len2 <= len
    {
      basic_mod(start + len1 + len2, len)
    }

    function InMemoryJournalFrozen() : seq<JournalEntry>
    requires WF()
    {
      cyclicSlice(journalEntries, start, len1)
    }

    function InMemoryJournal() : seq<JournalEntry>
    requires WF()
    {
      cyclicSlice(journalEntries, mid(|journalEntries| as uint64), len2)
    }

    function ReplayJournal() : seq<JournalEntry>
    requires 0 <= replayIdx as int <= |replayJournal|
    {
      replayJournal[replayIdx..]
    }

    // function JournalFrontRead() : Option<JournalRange>
    // requires WF()
    // {
    //   journalFront
    // }

    // function JournalBackRead() : Option<JournalRange>
    // requires WF()
    // {
    //   journalBack
    // }

    // function WrittenJournalLen() : int
    // {
    //   writtenJournalBlocks as int
    // }

    function Iprivate() : JournalInfo
    requires WF()
    {
      JournalInfo(
        InMemoryJournalFrozen(),
        InMemoryJournal(),
        ReplayJournal(),
        journalFront,
        journalBack,
        writtenJournalBlocks as int
      )
    }

    protected function I() : JournalInfo
    requires WF()
    {
      Iprivate()
    }

    lemma reveal_I()
    requires WF()
    ensures I() == Iprivate()
    {
    }

    static method Constructor() returns (linear j: Journalist)
    ensures j.Inv()
    ensures j.I().inMemoryJournalFrozen == []
    ensures j.I().inMemoryJournal == []
    ensures j.I().replayJournal == []
    ensures j.I().journalFront == None
    ensures j.I().journalBack == None
    ensures j.I().writtenJournalLen == 0
    {
      reveal_cyclicSlice();
      reveal_WeightJournalEntries();

      var newArray := NativeArrays.newArrayFill(4096, JournalInsert([], [])); 
    
      j := Journalist(
        newArray[..], 0, 0, 0,
        [], 0, None, None, 0, 0, 0);
    }

    shared method hasFrozenJournal() returns (b: bool)
    requires Inv()
    ensures b == (I().inMemoryJournalFrozen != [])
    {
      return len1 != 0;
    }

    shared method hasInMemoryJournal() returns (b: bool)
    requires Inv()
    ensures b == (I().inMemoryJournal != [])
    {
      return len2 != 0;
    }

    linear inout method packageFrozenJournal() returns (s: seq<byte>)
    requires old_self.Inv()
    requires old_self.I().inMemoryJournalFrozen != []
    ensures 
      && self.Inv()
      && JournalRangeOfByteSeq(s).Some?
      && parseJournalRange(JournalRangeOfByteSeq(s).value) == Some(old_self.I().inMemoryJournalFrozen)
      && self.I() == old_self.I()
            .(inMemoryJournalFrozen := [])
            .(writtenJournalLen := old_self.I().writtenJournalLen
                  + |JournalRangeOfByteSeq(s).value|)
      && |JournalRangeOfByteSeq(s).value| + old_self.I().writtenJournalLen as int
          <= NumJournalBlocks() as int
    {
      reveal_WeightJournalEntries();

      s := MarshallJournalEntries(
        self.journalEntries,
        self.start,
        self.len1,
        self.frozenJournalBlocks);

      inout self.start := basic_mod(self.start + self.len1,
          |self.journalEntries| as uint64);
      inout self.len1 := 0;
      inout self.writtenJournalBlocks :=
          self.writtenJournalBlocks + self.frozenJournalBlocks;
      inout self.frozenJournalBlocks := 0;
    }

    linear inout method packageInMemoryJournal() returns (s: seq<byte>)
    requires old_self.Inv()
    requires old_self.I().inMemoryJournalFrozen == []
    requires old_self.I().inMemoryJournal != []
    ensures
      && self.Inv()
      && JournalRangeOfByteSeq(s).Some?
      && parseJournalRange(JournalRangeOfByteSeq(s).value) == Some(old_self.I().inMemoryJournal)
      && self.I() == old_self.I()
            .(inMemoryJournal := [])
            .(writtenJournalLen := old_self.I().writtenJournalLen
                  + |JournalRangeOfByteSeq(s).value|)
      && |JournalRangeOfByteSeq(s).value| + old_self.I().writtenJournalLen as int
          <= NumJournalBlocks() as int
    {
      reveal_WeightJournalEntries();

      var numBlocks := (self.inMemoryWeight + 4064 - 1) / 4064;
      s := MarshallJournalEntries(
        self.journalEntries,
        self.start,
        self.len2,
        numBlocks);

      inout self.start := 0;
      inout self.len2 := 0;
      inout self.inMemoryWeight := 0;
      inout self.writtenJournalBlocks := self.writtenJournalBlocks + numBlocks;
    }

    shared method getWrittenJournalLen()
    returns (len : uint64)
    requires Inv()
    ensures len as int == I().writtenJournalLen
    {
      return writtenJournalBlocks;
    }

    linear inout method setWrittenJournalLen(len: uint64)
    requires old_self.Inv()
    requires old_self.I().inMemoryJournal == []
    requires old_self.I().inMemoryJournalFrozen == []
    requires 0 <= len <= NumJournalBlocks()

    ensures self.Inv()
    ensures self.I() == old_self.I().(writtenJournalLen := len as int)
    {
      reveal_WeightJournalEntries();
      inout self.writtenJournalBlocks := len;
      inout self.frozenJournalBlocks := 0;
    }

    linear inout method updateWrittenJournalLen(len: uint64)
    requires old_self.Inv()
    requires len as int <= old_self.I().writtenJournalLen
    ensures self.Inv()
    ensures self.I() == old_self.I().(writtenJournalLen := len as int)
    {
      inout self.writtenJournalBlocks := len;
    }

    linear inout method freeze()
    requires old_self.Inv()
    ensures 
      && self.Inv()
      && self.I() == old_self.I()
        .(inMemoryJournal := [])
        .(inMemoryJournalFrozen :=
          old_self.I().inMemoryJournalFrozen + old_self.I().inMemoryJournal)
    {
      reveal_WeightJournalEntries();

      inout self.len1 := self.len1 + self.len2;
      inout self.len2 := 0;
      inout self.frozenJournalBlocks := self.frozenJournalBlocks
          + (self.inMemoryWeight + 4064 - 1) / 4064;
      inout self.inMemoryWeight := 0;

      assert self.I().inMemoryJournalFrozen ==
        old_self.I().inMemoryJournalFrozen + old_self.I().inMemoryJournal
      by { reveal_cyclicSlice(); }

      WeightJournalEntriesSum(old_self.I().inMemoryJournalFrozen, old_self.I().inMemoryJournal);
    }

    protected shared function method canAppend(je: JournalEntry) : (b : bool)
    requires Inv()
    {
      4064 * (writtenJournalBlocks + frozenJournalBlocks)
          + inMemoryWeight
          + WeightJournalEntryUint64(je)
          + (if len2 == 0 then 8 else 0)
        <= 4064 * NumJournalBlocks()
    }

    linear inout method append(je: JournalEntry)
    requires old_self.Inv()
    requires old_self.canAppend(je)
    ensures self.Inv()
    ensures self.I() == old_self.I().(inMemoryJournal := old_self.I().inMemoryJournal + [je])
    {
      lenTimes8LeWeight(self.InMemoryJournal());
      lenTimes8LeWeight(self.InMemoryJournalFrozen());

      if self.len1 + self.len2 < |self.journalEntries| as uint64 {
        var idx := basic_mod(
            self.start + self.len1 + self.len2,
            |self.journalEntries| as uint64);
        inout self.journalEntries := self.journalEntries[idx as int := je];
      } else {
        var newLen: uint64 := |self.journalEntries| as uint64 * 2;
        var newArray := NativeArrays.newArrayFill(
            newLen,
            JournalInsert([], []));

        NativeArrays.CopySeqIntoArray(
            self.journalEntries,
            self.start,
            newArray,
            0,
            |self.journalEntries| as uint64 - self.start);

        NativeArrays.CopySeqIntoArray(
            self.journalEntries,
            0,
            newArray,
            |self.journalEntries| as uint64 - self.start,
            self.start);

        newArray[|self.journalEntries| as uint64] := je;

        calc {
          newArray[..];
          self.journalEntries[self.start..]
            + self.journalEntries[..self.start]
            + [je]
            + fill((newLen as int - |self.journalEntries| - 1) as int, JournalInsert([], []));
        }

        inout self.journalEntries := newArray[..];
        inout self.start := 0;
      }

      inout self.inMemoryWeight := self.inMemoryWeight
          + WeightJournalEntryUint64(je)
          + (if self.len2 == 0 then 8 else 0);
      inout self.len2 := self.len2 + 1;

      assert self.InMemoryJournal()
        == old_self.InMemoryJournal() + [je] by { reveal_cyclicSlice(); }
      assert self.InMemoryJournalFrozen()
        == old_self.InMemoryJournalFrozen() by { reveal_cyclicSlice(); }
      lemma_weight_append(old_self.InMemoryJournal(), je);
    }

    shared method isReplayEmpty()
    returns (b: bool)
    requires Inv()
    ensures b == (I().replayJournal == [])
    {
      b := (replayIdx == |replayJournal| as uint64);
    }

    shared function method replayJournalTop() : (je: JournalEntry)
    requires Inv()
    requires I().replayJournal != []
    ensures je == I().replayJournal[0]
    {
      replayJournal[replayIdx]
    }

    inout linear method replayJournalPop()
    requires old_self.Inv()
    requires old_self.I().replayJournal != []
    ensures self.Inv()
    ensures self.I() == old_self.I().(replayJournal := self.I().replayJournal)
    ensures old_self.I().replayJournal
        == [old_self.replayJournalTop()] + self.I().replayJournal
    {
      inout self.replayIdx := self.replayIdx + 1;
    }

    inout linear method setFront(jr: JournalRange)
    requires old_self.Inv()
    requires forall i | 0 <= i < |jr| :: |jr[i]| == 4064
    requires |jr| <= NumJournalBlocks() as int
    ensures self.Inv()
    ensures self.I() == old_self.I().(journalFront := Some(jr))
    {
      inout self.journalFront := Some(jr);
    }

    inout linear method setBack(jr: JournalRange)
    requires old_self.Inv()
    requires forall i | 0 <= i < |jr| :: |jr[i]| == 4064
    requires |jr| <= NumJournalBlocks() as int
    ensures self.Inv()
    ensures self.I() == old_self.I().(journalBack := Some(jr))
    {
      inout self.journalBack := Some(jr);
    }

    inout linear method parseJournals() returns (success: bool)
    requires old_self.Inv()
    ensures self.Inv()
    ensures
      var old_I := old_self.I();
      && self.Inv()
      && (!success ==> self.I() == old_I)
      && (success ==>
        var fullRange :=
          (if old_I.journalFront.Some? then old_I.journalFront.value
              else []) +
          (if old_I.journalBack.Some? then old_I.journalBack.value
              else []);
        && parseJournalRange(fullRange).Some?
        && self.I() == old_I
            .(journalFront := None)
            .(journalBack := None)
            .(replayJournal := parseJournalRange(fullRange).value));
    {
      var fullRange :=
        (if self.journalFront.Some? then self.journalFront.value else []) +
        (if self.journalBack.Some? then self.journalBack.value else []);
      var p := JournalistParsingImpl.ParseJournalRange(fullRange);
      if p.Some? && |p.value| as uint64 <= MaxPossibleEntries() {
        inout self.journalFront := None;
        inout self.journalBack := None;
        inout self.replayJournal := p.value;
        inout self.replayIdx := 0;
        success := true;
      } else {
        success := false;
      }
    }

    shared method hasFront()
    returns (b: bool)
    requires Inv()
    ensures b == I().journalFront.Some?
    {
      b := journalFront.Some?;
    }

    shared method hasBack()
    returns (b: bool)
    requires Inv()
    ensures b == I().journalBack.Some?
    {
      b := journalBack.Some?;
    }
  }
}
