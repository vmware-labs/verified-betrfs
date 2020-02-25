include "../MapSpec/Journal.i.dfy"

module JournalRanges {
  import opened KeyType 
  import opened ValueMessage
  import opened Journal

  // Range of JournalEntries in a form that can be written
  // as a series of blocks on disk, or an incomplete chunk of
  // such a list.
  type JournalRange

  predicate JournalRangeParses(jr: JournalRange, jes: seq<JournalEntry>)

  function JournalRangeLen(jr: JournalRange) : (len : int)
  ensures len >= 0

  function JournalRangePrefix(jr: JournalRange, i: int) : JournalRange
  requires 0 <= i <= JournalRangeLen(jr)

  function JournalRangeConcat(jr1: JournalRange, jr2: JournalRange) : JournalRange
  function JournalRangeEmpty() : JournalRange

  function JournalRangeSuffix(jr: JournalRange, i: int) : JournalRange
  requires 0 <= i <= JournalRangeLen(jr)
}
