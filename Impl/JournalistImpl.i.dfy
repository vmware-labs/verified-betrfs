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
    function method MaxPossibleEntries() : uint64 { 32*1048576 }

    predicate WF()
    {
      && 1 <= |this.journalEntries| <= 2 * MaxPossibleEntries() as int
      && 0 <= this.start < |this.journalEntries| as uint64
      && 0 <= this.len1 <= |this.journalEntries| as uint64
      && 0 <= this.len2 <= |this.journalEntries| as uint64
      && 0 <= this.len1 + this.len2 <= |this.journalEntries| as uint64
      && 0 <= this.replayIdx as int <= |this.replayJournal| <= MaxPossibleEntries() as int
      && (this.journalFront.Some? ==>
          CorrectJournalBlockSizes(this.journalFront.value))
      && (this.journalBack.Some? ==>
          CorrectJournalBlockSizes(this.journalBack.value))
      && 0 <= this.writtenJournalBlocks <= NumJournalBlocks()
      && 0 <= this.frozenJournalBlocks <= NumJournalBlocks()
      && 0 <= this.inMemoryWeight <= NumJournalBlocks() * 4096
    }

    predicate Inv()
    {
      && WF()
      && (this.writtenJournalBlocks + this.frozenJournalBlocks) * 4064 +
          this.inMemoryWeight <= 4064 * NumJournalBlocks()
      && WeightJournalEntries(InMemoryJournalFrozen()) <= this.frozenJournalBlocks as int * 4064
      && WeightJournalEntries(InMemoryJournal()) == this.inMemoryWeight as int
    }

    function mid(len: uint64) : uint64
    requires len <= 2 * MaxPossibleEntries()
    requires this.start < len
    requires this.len1 <= len
    {
      basic_mod(this.start + this.len1, len)
    }

    function end(len: uint64) : uint64
    requires len <= 2 * MaxPossibleEntries()
    requires this.start < len
    requires this.len1 <= len
    requires this.len2 <= len
    {
      basic_mod(this.start + this.len1 + this.len2, len)
    }

    function InMemoryJournalFrozen() : seq<JournalEntry>
    requires WF()
    {
      cyclicSlice(this.journalEntries, this.start, this.len1)
    }

    function InMemoryJournal() : seq<JournalEntry>
    requires WF()
    {
      cyclicSlice(this.journalEntries,
        mid(|this.journalEntries| as uint64),
        this.len2)
    }

    function ReplayJournal() : seq<JournalEntry>
    requires 0 <= this.replayIdx as int <= |this.replayJournal|
    {
      this.replayJournal[this.replayIdx..]
    }

    function JournalFrontRead() : Option<JournalRange>
    requires WF()
    {
      this.journalFront
    }

    function JournalBackRead() : Option<JournalRange>
    requires WF()
    {
      this.journalBack
    }

    function WrittenJournalLen() : int
    {
      this.writtenJournalBlocks as int
    }

    function Iprivate() : JournalInfo
    requires WF()
    {
      JournalInfo(
        InMemoryJournalFrozen(),
        InMemoryJournal(),
        ReplayJournal(),
        JournalFrontRead(),
        JournalBackRead(),
        WrittenJournalLen()
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

/*
    shared method hasFrozenJournal() returns (b: bool)
    requires Inv()
    ensures b == JournalistModel.hasFrozenJournal(I())
    {
      JournalistModel.reveal_hasFrozenJournal();
      return this.len1 != 0;
    }

    shared method hasInMemoryJournal() returns (b: bool)
    requires Inv()
    ensures b == JournalistModel.hasInMemoryJournal(I())
    {
      JournalistModel.reveal_hasInMemoryJournal();
      return this.len2 != 0;
    }

    linear inout method packageFrozenJournal() returns (s: seq<byte>)
    requires old_self.Inv()
    requires JournalistModel.packageFrozenJournal.requires(old_self.I())
    ensures self.Inv()
    ensures (self.I(), s) == JournalistModel.packageFrozenJournal(old_self.I())
    {
      JournalistModel.reveal_packageFrozenJournal();
      reveal_WeightJournalEntries();
      JournalistModel.reveal_I(old_self.I());

      s := MarshallJournalEntries(
        self.journalEntries,
        self.start,
        self.len1,
        self.frozenJournalBlocks);

      inout self.start := JournalistModel.basic_mod(self.start + self.len1,
          |self.journalEntries| as uint64);
      inout self.len1 := 0;
      inout self.writtenJournalBlocks :=
          self.writtenJournalBlocks + self.frozenJournalBlocks;
      inout self.frozenJournalBlocks := 0;
    }

    linear inout method packageInMemoryJournal() returns (s: seq<byte>)
    requires old_self.Inv()
    requires JournalistModel.packageInMemoryJournal.requires(old_self.I())
    ensures self.Inv()
    ensures (self.I(), s) == JournalistModel.packageInMemoryJournal(old_self.I())
    {
      JournalistModel.reveal_packageInMemoryJournal();
      reveal_WeightJournalEntries();
      JournalistModel.reveal_I(old_self.I());

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
    ensures len == JournalistModel.getWrittenJournalLen(I())
    {
      return this.writtenJournalBlocks;
    }

    linear inout method setWrittenJournalLen(len: uint64)
    requires old_self.Inv()
    requires JournalistModel.setWrittenJournalLen.requires(old_self.I(), len)
    ensures self.Inv()
    ensures self.I() == JournalistModel.setWrittenJournalLen(old_self.I(), len)
    {
      inout self.writtenJournalBlocks := len;
      inout self.frozenJournalBlocks := 0;
      assert self.I() == JournalistModel.setWrittenJournalLen(old_self.I(), len);
    }

    linear inout method updateWrittenJournalLen(len: uint64)
    requires old_self.Inv()
    requires JournalistModel.updateWrittenJournalLen.requires(old_self.I(), len)
    ensures self.Inv()
    ensures self.I() == JournalistModel.updateWrittenJournalLen(old_self.I(), len)
    {
      inout self.writtenJournalBlocks := len;
      assert self.I() ==
        JournalistModel.updateWrittenJournalLen(old_self.I(), len);
    }

    linear inout method freeze()
    requires old_self.Inv()
    ensures self.Inv()
    ensures self.I() == JournalistModel.freeze(old_self.I())
    {
      JournalistModel.reveal_freeze();

      inout self.len1 := self.len1 + self.len2;
      inout self.len2 := 0;
      inout self.frozenJournalBlocks := self.frozenJournalBlocks
          + (self.inMemoryWeight + 4064 - 1) / 4064;
      inout self.inMemoryWeight := 0;

      assert self.I() == JournalistModel.freeze(old_self.I());
    }

    protected shared function method canAppend(je: JournalEntry) : (b : bool)
    // returns (b: bool)
    requires Inv()
    ensures b == JournalistModel.canAppend(I(), je)
    {
      JournalistModel.reveal_canAppend();

      4064 * (writtenJournalBlocks + frozenJournalBlocks)
          + inMemoryWeight
          + WeightJournalEntryUint64(je)
          + (if len2 == 0 then 8 else 0)
        <= 4064 * NumJournalBlocks()
    }

    linear inout method append(je: JournalEntry)
    requires old_self.Inv()
    requires JournalistModel.canAppend(old_self.I(), je)
    ensures self.Inv()
    ensures self.I() == JournalistModel.append(old_self.I(), je)
    {
      JournalistModel.reveal_append();

      if self.len1 + self.len2 < |self.journalEntries| as uint64 {
        var idx := JournalistModel.basic_mod(
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

      assert self.I() == JournalistModel.append(old_self.I(), je);
    }

    shared method isReplayEmpty()
    returns (b: bool)
    requires Inv()
    ensures b == JournalistModel.isReplayEmpty(I())
    {
      JournalistModel.reveal_isReplayEmpty();
      b := (replayIdx == |replayJournal| as uint64);
    }

    shared method replayJournalTop()
    returns (je: JournalEntry)
    requires Inv()
    requires JournalistModel.I(I()).replayJournal != []
    ensures je == JournalistModel.replayJournalTop(I())
    {
      JournalistModel.reveal_replayJournalTop();
      JournalistModel.reveal_I(I());
      je := replayJournal[replayIdx];
    }

    inout linear method replayJournalPop()
    requires old_self.Inv()
    requires JournalistModel.I(old_self.I()).replayJournal != []
    ensures self.Inv()
    ensures self.I() == JournalistModel.replayJournalPop(old_self.I())
    {
      JournalistModel.reveal_replayJournalPop();
      JournalistModel.reveal_I(old_self.I());
      inout self.replayIdx := self.replayIdx + 1;
    }

    inout linear method setFront(jr: JournalRange)
    requires old_self.Inv()
    requires forall i | 0 <= i < |jr| :: |jr[i]| == 4064
    requires |jr| <= NumJournalBlocks() as int
    ensures self.Inv()
    ensures self.I() == JournalistModel.setFront(old_self.I(), jr)
    {
      JournalistModel.reveal_setFront();
      inout self.journalFront := Some(jr);
    }

    inout linear method setBack(jr: JournalRange)
    requires old_self.Inv()
    requires forall i | 0 <= i < |jr| :: |jr[i]| == 4064
    requires |jr| <= NumJournalBlocks() as int
    ensures self.Inv()
    ensures self.I() == JournalistModel.setBack(old_self.I(), jr)
    {
      JournalistModel.reveal_setBack();
      inout self.journalBack := Some(jr);
    }

    inout linear method parseJournals() returns (success: bool)
    requires old_self.Inv()
    ensures self.Inv()
    ensures (self.I(), success) == JournalistModel.parseJournals(old_self.I())
    {
      JournalistModel.reveal_parseJournals();
      JournalistModel.reveal_I(old_self.I());
      var fullRange :=
        (if self.journalFront.Some? then self.journalFront.value else []) +
        (if self.journalBack.Some? then self.journalBack.value else []);
      var p := JournalistParsingImpl.ParseJournalRange(fullRange);
      if p.Some? && |p.value| as uint64 <= JournalistModel.MaxPossibleEntries() {
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
    ensures b == JournalistModel.hasFront(I())
    {
      JournalistModel.reveal_hasFront();
      b := journalFront.Some?;
    }

    shared method hasBack()
    returns (b: bool)
    requires Inv()
    ensures b == JournalistModel.hasBack(I())
    {
      JournalistModel.reveal_hasBack();
      b := journalBack.Some?;
    }
  */
  }
}
