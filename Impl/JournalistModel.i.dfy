include "../ByteBlockCacheSystem/JournalBytes.i.dfy"
include "../BlockCacheSystem/DiskLayout.i.dfy"

module JournalistModel {
  import opened JournalRanges
  import opened JournalBytes
  import opened Journal
  import opened DiskLayout
  import opened NativeTypes
  import opened Options

  datatype JournalInfo = JournalInfo(
    inMemoryJournalFrozen: seq<JournalEntry>,
    inMemoryJournal: seq<JournalEntry>,
    replayJournal: seq<JournalEntry>,

    journalFrontRead: Option<JournalRange>,
    journalBackRead: Option<JournalRange>
  )

  datatype JournalistModel = JournalistModel(
    journalEntries: seq<JournalEntry>,
    fStart: uint64,
    fLen: uint64,
    eStart: uint64,
    eLen: uint64,

    replayJournal: seq<JournalEntry>,
    replayIdx: uint64,

    journalFrontRead: Option<seq<byte>>,
    journalBackRead: Option<seq<byte>>)

  function method Len() : uint64 { 1048576 }

  predicate WF(jm: JournalistModel)
  {
    && |jm.journalEntries| == Len() as int
    && 0 <= jm.fStart < Len()
    && 0 <= jm.fLen <= Len()
    && 0 <= jm.eStart < Len()
    && 0 <= jm.eLen <= Len()
    && 0 <= jm.replayIdx as int <= |jm.replayJournal|
    && (jm.journalFrontRead.Some? ==>
        JournalRangeOfByteSeq(jm.journalFrontRead.value).Some?)
    && (jm.journalBackRead.Some? ==>
        JournalRangeOfByteSeq(jm.journalBackRead.value).Some?)
  }

  function cyclicSlice<T>(t: seq<T>, start: uint64, l: uint64) : seq<T>
  requires 0 <= start as int < |t|
  requires 0 <= l as int <= |t|
  {
    if start as int + l as int <= |t| then
      t[start .. start + l]
    else
      t[start ..] + t[.. start + l - |t| as uint64]
  }

  function IJournalRead(j: Option<seq<byte>>) : Option<JournalRange>
  requires j.Some? ==> JournalRangeOfByteSeq(j.value).Some?
  {
    if j.Some? then JournalRangeOfByteSeq(j.value) else None
  }
    
  protected function I(jm: JournalistModel) : JournalInfo
  requires WF(jm)
  {
    JournalInfo(
      cyclicSlice(jm.journalEntries, jm.fStart, jm.fLen),
      cyclicSlice(jm.journalEntries, jm.eStart, jm.eLen),
      replayJournal[replayIdx..],
      IJournalRead(jm.journalFrontRead),
      IJournalRead(jm.journalBackRead)
    )
  }
}
