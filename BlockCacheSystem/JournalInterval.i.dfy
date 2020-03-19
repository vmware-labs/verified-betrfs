include "JournalRange.i.dfy"
include "DiskLayout.i.dfy"

module JournalIntervals {
  import opened DiskLayout
  import opened JournalRanges
  import opened Options

  datatype JournalInterval = JournalInterval(start: int, len: int)

  predicate ValidJournalInterval(indices: JournalInterval)
  {
    && 0 <= indices.start < NumJournalBlocks() as int
    && 0 <= indices.len <= NumJournalBlocks() as int
  }

  predicate ContiguousJournalInterval(indices: JournalInterval)
  {
    && ValidJournalInterval(indices)
    && 0 <= indices.start + indices.len <= NumJournalBlocks() as int
  }

  predicate ValidJournal(journal: seq<Option<JournalBlock>>)
  {
    |journal| == NumJournalBlocks() as int
  }

  function CyclicSliceValue(
    journal: seq<Option<JournalBlock>>,
    indices: JournalInterval,
    newEntries: seq<JournalBlock>,
    i: int
  ) : Option<JournalBlock>
  requires ValidJournal(journal)
  requires ValidJournalInterval(indices)
  requires indices.len == |newEntries|
  requires 0 <= i < NumJournalBlocks() as int
  {
    if indices.start <= i < indices.start + indices.len then
      Some(newEntries[i - indices.start])
    else if indices.start <= i + NumJournalBlocks() as int < indices.start + indices.len then
      Some(newEntries[i + NumJournalBlocks() as int - indices.start])
    else
      journal[i]
  }

  predicate {:opaque} JournalUpdate(
      journal: seq<Option<JournalBlock>>,
      journal': seq<Option<JournalBlock>>,
      indices: JournalInterval,
      newEntries: seq<JournalBlock>)
  {
    && ValidJournal(journal)
    && ValidJournal(journal')
    && ValidJournalInterval(indices)
    && indices.len == |newEntries|
    && (forall i | 0 <= i < |journal| ::
        journal'[i] == CyclicSliceValue(journal, indices, newEntries, i))
  }

  predicate InCyclicRange(i: int, indices: JournalInterval)
  {
    || (indices.start <= i < indices.start + indices.len)
    || (indices.start <= i + NumJournalBlocks() as int < indices.start + indices.len)
  }

  function JournalFrontInterval(start: int, len: int) : Option<JournalInterval>
  requires start < NumJournalBlocks() as int
  {
    if len == 0 then
      None
    else
      Some(JournalInterval(
          start,
          if len <= NumJournalBlocks() as int - start
          then
            len
          else
            NumJournalBlocks() as int - start
      ))
  }

  function JournalBackInterval(start: int, len: int) : Option<JournalInterval>
  requires start < NumJournalBlocks() as int
  requires len <= NumJournalBlocks() as int
  {
    if len == 0 then
      None
    else if len <= NumJournalBlocks() as int - start then
      None
    else
      Some(JournalInterval(0, 
          len - (NumJournalBlocks() as int - start)))

  }
}
