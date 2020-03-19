include "JournalRange.i.dfy"
include "DiskLayout.i.dfy"

module JournalDisk {
  import opened DiskLayout
  import opened JournalRanges
  import opened Options

  datatype JournalIndices = JournalIndices(start: int, len: int)

  predicate ValidJournalIndices(indices: JournalIndices)
  {
    && 0 <= indices.start < NumJournalBlocks() as int
    && 0 <= indices.len <= NumJournalBlocks() as int
  }

  predicate ValidJournal(journal: seq<Option<JournalBlock>>)
  {
    |journal| == NumJournalBlocks() as int
  }

  function CyclicSliceValue(
    journal: seq<Option<JournalBlock>>,
    indices: JournalIndices,
    newEntries: seq<JournalBlock>,
    i: int
  ) : Option<JournalBlock>
  requires ValidJournal(journal)
  requires ValidJournalIndices(indices)
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
      indices: JournalIndices,
      newEntries: seq<JournalBlock>)
  {
    && ValidJournal(journal)
    && ValidJournal(journal')
    && ValidJournalIndices(indices)
    && indices.len == |newEntries|
    && (forall i | 0 <= i < |journal| ::
        journal'[i] == CyclicSliceValue(journal, indices, newEntries, i))
  }

  predicate InCyclicRange(i: int, indices: JournalIndices)
  {
    || (indices.start <= i < indices.start + indices.len)
    || (indices.start <= i + NumJournalBlocks() as int < indices.start + indices.len)
  }
}
