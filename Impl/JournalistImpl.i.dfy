include "JournalistModel.i.dfy"
include "../lib/Lang/System/NativeArrays.s.dfy"
include "JournalistMarshallingImpl.i.dfy"
include "JournalistParsingImpl.i.dfy"

module JournalistImpl {
  import opened DiskLayout
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import NativeArrays

  import opened JournalRanges`Internal
  import opened JournalBytes
  import opened Journal
  import JournalistMarshallingModel
  import opened JournalistMarshallingImpl
  import JournalistParsingImpl

  import JournalistModel

  linear datatype Journalist = Journalist(journalEntries: seq<JournalEntry>, start: uint64,
    len1: uint64, len2: uint64, replayJournal: seq<JournalEntry>, replayIdx: uint64, 
    journalFront: Option<seq<JournalBlock>>, journalBack: Option<seq<JournalBlock>>, writtenJournalBlocks: uint64,
    frozenJournalBlocks: uint64, inMemoryWeight: uint64)
  {
    function I() : JournalistModel.JournalistModel
    {
      JournalistModel.JournalistModel(
        this.journalEntries[..],
        this.start,
        this.len1,
        this.len2,
        this.replayJournal,
        this.replayIdx,
        this.journalFront,
        this.journalBack,
        this.writtenJournalBlocks,
        this.frozenJournalBlocks,
        this.inMemoryWeight)
    }

    predicate WF()
    {
      && JournalistModel.WF(I())
    }

    predicate Inv()
    {
      && JournalistModel.Inv(I())
    }

    static method NewJournal() returns (linear j: Journalist)
    ensures j.Inv()
    ensures j.I() == JournalistModel.JournalistConstructor()
    {
      var temp := NativeArrays.newArrayFill(4096, JournalInsert([], [])); 
    
      j := Journalist(
        temp[..], 0, 0, 0,
        [], 0, None, None, 0, 0, 0);

      JournalistModel.reveal_JournalistConstructor();
      assert j.I() == JournalistModel.JournalistConstructor();
    }

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

    shared method canAppend(je: JournalEntry)
    returns (b: bool)
    requires Inv()
    ensures b == JournalistModel.canAppend(I(), je)
    {
      JournalistModel.reveal_canAppend();

      b := 4064 * (writtenJournalBlocks + frozenJournalBlocks)
          + inMemoryWeight
          + WeightJournalEntryUint64(je)
          + (if len2 == 0 then 8 else 0)
        <= 4064 * NumJournalBlocks();
    }

    // linear inout method append(je: JournalEntry)
    // requires old_self.Inv()
    // requires JournalistModel.canAppend(I(), je)
    // ensures self.Inv()
    // ensures self.I() == JournalistModel.append(old_self.I(), je)
    // {
    //   JournalistModel.reveal_append();

    //   if self.len1 + self.len2 < |self.journalEntries| as uint64 {
    //     var idx := JournalistModel.basic_mod(
    //         start + len1 + len2,
    //         |self.journalEntries| as uint64);
    //     inout self.journalEntries[idx] := je;
    //   } else {
    //     var newLen: uint64 := |self.journalEntries| as uint64 * 2;
    //     var newArray := NativeArrays.newArrayFill(
    //         newLen,
    //         JournalInsert([], []));
    //     NativeArrays.CopyArrayIntoDifferentArray(
    //         self.journalEntries,
    //         self.start,
    //         newArray,
    //         0,
    //         |self.journalEntries| as uint64 - self.start);
    //     NativeArrays.CopyArrayIntoDifferentArray(
    //         self.journalEntries,
    //         0,
    //         newArray,
    //         |self.journalEntries| as uint64 - self.start,
    //         self.start);
    //     newArray[|self.journalEntries| as uint64] := je;

    //     calc {
    //       newArray[..];
    //       self.journalEntries[start..]
    //         + self.journalEntries[..start]
    //         + [je]
    //         + fill((newLen as int - |self.journalEntries| - 1) as int, JournalInsert([], []));
    //     }

    //     inout self.journalEntries := newArray;
    //     inout self.start := 0;
    //   }

    //   inout self.inMemoryWeight := self.inMemoryWeight
    //       + WeightJournalEntryUint64(je)
    //       + (if self.len2 == 0 then 8 else 0);
    //   inout self.len2 := self.len2 + 1;

    //   assert self.I() == JournalistModel.append(old_self.I(), je);
    // }

  //   method isReplayEmpty()
  //   returns (b: bool)
  //   requires Inv()
  //   ensures b == JournalistModel.isReplayEmpty(I())
  //   {
  //     JournalistModel.reveal_isReplayEmpty();
  //     b := (replayIdx == |replayJournal| as uint64);
  //   }

  //   method replayJournalTop()
  //   returns (je: JournalEntry)
  //   requires Inv()
  //   requires JournalistModel.I(I()).replayJournal != []
  //   ensures je == JournalistModel.replayJournalTop(I())
  //   {
  //     JournalistModel.reveal_replayJournalTop();
  //     JournalistModel.reveal_I(I());
  //     je := replayJournal[replayIdx];
  //   }

  //   method replayJournalPop()
  //   requires Inv()
  //   requires JournalistModel.I(I()).replayJournal != []
  //   modifies Repr
  //   ensures Inv()
  //   ensures Repr == old(Repr)
  //   ensures I() == JournalistModel.replayJournalPop(old_self.I())
  //   {
  //     JournalistModel.reveal_replayJournalPop();
  //     JournalistModel.reveal_I(I());
  //     replayIdx := replayIdx + 1;
  //   }

  //   method setFront(jr: JournalRange)
  //   requires Inv()
  //   requires forall i | 0 <= i < |jr| :: |jr[i]| == 4064
  //   requires |jr| <= NumJournalBlocks() as int
  //   modifies Repr
  //   ensures Inv()
  //   ensures Repr == old(Repr)
  //   ensures I() == JournalistModel.setFront(old_self.I(), jr)
  //   {
  //     JournalistModel.reveal_setFront();
  //     journalFront := Some(jr);
  //   }

  //   method setBack(jr: JournalRange)
  //   requires Inv()
  //   requires forall i | 0 <= i < |jr| :: |jr[i]| == 4064
  //   requires |jr| <= NumJournalBlocks() as int
  //   modifies Repr
  //   ensures Inv()
  //   ensures Repr == old(Repr)
  //   ensures I() == JournalistModel.setBack(old_self.I(), jr)
  //   {
  //     JournalistModel.reveal_setBack();
  //     journalBack := Some(jr);
  //   }

  //   method parseJournals()
  //   returns (success: bool)
  //   requires Inv()
  //   modifies Repr
  //   ensures Inv()
  //   ensures Repr == old(Repr)
  //   ensures (I(), success) == JournalistModel.parseJournals(old_self.I())
  //   {
  //     JournalistModel.reveal_parseJournals();
  //     JournalistModel.reveal_I(I());
  //     var fullRange :=
  //       (if journalFront.Some? then journalFront.value else []) +
  //       (if journalBack.Some? then journalBack.value else []);
  //     var p := JournalistParsingImpl.ParseJournalRange(fullRange);
  //     if p.Some? && |p.value| as uint64 <= JournalistModel.MaxPossibleEntries() {
  //       journalFront := None;
  //       journalBack := None;
  //       replayJournal := p.value;
  //       replayIdx := 0;
  //       return true;
  //     } else {
  //       return false;
  //     }
  //   }

  //   method hasFront()
  //   returns (b: bool)
  //   requires Inv()
  //   ensures b == JournalistModel.hasFront(I())
  //   {
  //     JournalistModel.reveal_hasFront();
  //     b := journalFront.Some?;
  //   }

  //   method hasBack()
  //   returns (b: bool)
  //   requires Inv()
  //   ensures b == JournalistModel.hasBack(I())
  //   {
  //     JournalistModel.reveal_hasBack();
  //     b := journalBack.Some?;
  //   }
  }
}
