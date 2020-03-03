include "../MapSpec/Journal.i.dfy"
include "../lib/Base/Option.s.dfy"

module JournalRanges {
  import opened KeyType 
  import opened ValueMessage
  import opened Journal
  import opened Options

  // Range of JournalEntries in a form that can be written
  // as a series of blocks on disk, or an incomplete chunk of
  // such a list.
  type JournalRange

  function parseJournalRange(jr: JournalRange) : Option<seq<JournalEntry>>

  predicate JournalRangeParses(jr: JournalRange, jes: seq<JournalEntry>)
  {
    parseJournalRange(jr) == Some(jes)
  }

  function JournalRangeLen(jr: JournalRange) : (len : int)
  ensures len >= 0

  function JournalRangePrefix(jr: JournalRange, i: int) : JournalRange
  requires 0 <= i <= JournalRangeLen(jr)

  function JournalRangeConcat(jr1: JournalRange, jr2: JournalRange) : JournalRange
  function JournalRangeEmpty() : JournalRange

  function JournalRangeSuffix(jr: JournalRange, i: int) : JournalRange
  requires 0 <= i <= JournalRangeLen(jr)

  function JournalBlockGet(jr: JournalRange, i: int) : (res : JournalRange)
  requires 0 <= i < JournalRangeLen(jr)
  ensures JournalRangeLen(res) == 1

  function JournalBlocks(jr: JournalRange) : (res : seq<JournalRange>)
  ensures |res| == JournalRangeLen(jr)
  ensures forall i | 0 < i < |res| :: res[i] == JournalBlockGet(jr, i)

  lemma parseJournalRangeEmpty()
  ensures parseJournalRange(JournalRangeEmpty()) == Some([])

  lemma parseJournalRangeAdditive(a: JournalRange, b: JournalRange)
  requires parseJournalRange(a).Some?
  requires parseJournalRange(b).Some?
  ensures parseJournalRange(JournalRangeConcat(a, b)).Some?
  ensures parseJournalRange(JournalRangeConcat(a, b)).value
      == parseJournalRange(a).value + parseJournalRange(b).value

  lemma JournalRangeConcatAssoc(a: JournalRange, b: JournalRange, c: JournalRange)
  ensures JournalRangeConcat(JournalRangeConcat(a, b), c)
       == JournalRangeConcat(a, JournalRangeConcat(b, c))

  lemma JournalRangeConcatEmpty(a: JournalRange)
  ensures JournalRangeConcat(a, JournalRangeEmpty()) == a

  lemma JournalRangeConcatEmpty'(a: JournalRange)
  ensures JournalRangeConcat(JournalRangeEmpty(), a) == a
}
