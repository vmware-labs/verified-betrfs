include "JournalRange.i.dfy"
include "DiskLayout.i.dfy"

module JournalIntervals {
  import opened DiskLayout
  import opened JournalRanges
  import opened Journal
  import opened Options
  import opened Sequences

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

  function CyclicSpliceValue(
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
  ensures JournalUpdate(journal, journal', indices, newEntries)
      ==> 
    && ValidJournal(journal)
    && ValidJournal(journal')
    && ValidJournalInterval(indices)
    && indices.len == |newEntries|
  {
    && ValidJournal(journal)
    && ValidJournal(journal')
    && ValidJournalInterval(indices)
    && indices.len == |newEntries|
    && (forall i | 0 <= i < |journal| ::
        journal'[i] == CyclicSpliceValue(journal, indices, newEntries, i))
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

  predicate subinterval(a: JournalInterval, b: JournalInterval)
  {
    || (a.start >= b.start && a.start + a.len <= b.start + b.len)
    || (a.start + NumJournalBlocks() as int >= b.start
        && a.start + NumJournalBlocks() as int + a.len <= b.start + b.len)
  }

  predicate journalIntervalOverlap(a: JournalInterval, b: JournalInterval)
  requires ContiguousJournalInterval(a)
  requires ContiguousJournalInterval(b)
  {
    && a.start + a.len > b.start
    && b.start + b.len > a.start
  }

  predicate journalCyclicIntervalOverlap(a: JournalInterval, b: JournalInterval)
  requires ValidJournalInterval(a)
  requires ValidJournalInterval(b)
  {
    if a.start + a.len > NumJournalBlocks() as int then (
      if b.start + b.len > NumJournalBlocks() as int then
        true
      else
        || journalIntervalOverlap(JournalInterval(a.start, NumJournalBlocks() as int - a.start), b)
        || journalIntervalOverlap(JournalInterval(0, a.len - (NumJournalBlocks() as int - a.start)), b)
    ) else (
      if b.start + b.len > NumJournalBlocks() as int then
        || journalIntervalOverlap(JournalInterval(b.start, NumJournalBlocks() as int - b.start), a)
        || journalIntervalOverlap(JournalInterval(0, b.len - (NumJournalBlocks() as int - b.start)), a)
      else
        journalIntervalOverlap(a, b)
    )
  }

  function {:opaque} CyclicSlice<T>(s: seq<T>, interval: JournalInterval) : seq<T>
  requires |s| == NumJournalBlocks() as int
  requires 0 <= interval.start < NumJournalBlocks() as int
  requires 0 <= interval.len <= NumJournalBlocks() as int
  {
    if interval.start + interval.len <= NumJournalBlocks() as int then
      s[interval.start .. interval.start + interval.len]
    else
      s[interval.start ..] +
        s[.. interval.start + interval.len - NumJournalBlocks() as int]
  }

  predicate fullRange(s: seq<Option<JournalBlock>>)
  {
    forall i | 0 <= i < |s| :: s[i].Some?
  }

  function concatFold(s: seq<Option<JournalBlock>>) : (res : seq<JournalBlock>)
  requires fullRange(s)
  ensures |res| == |s|
  ensures forall i | 0 <= i < |s| :: Some(res[i]) == s[i]
  {
    if s == [] then [] else
      concatFold(DropLast(s)) + [Last(s).value]
  }

  lemma concatFoldAdditive(
      a: seq<Option<JournalBlock>>,
      b: seq<Option<JournalBlock>>)
  requires fullRange(a)
  requires fullRange(b)
  ensures fullRange(a + b)
  ensures concatFold(a + b)
      == JournalRangeConcat(concatFold(a), concatFold(b))
  {
    if |b| == 0 {
      assert b == [];
      assert a + b == a;
      calc {
        concatFold(a + b);
        concatFold(a);
        {
          JournalRangeConcatEmpty(concatFold(a));
        }
        JournalRangeConcat(concatFold(a), JournalRangeEmpty());
        JournalRangeConcat(concatFold(a), concatFold(b));
      }
    } else {
      concatFoldAdditive(a, b[..|b|-1]);
      assert (a + b)[..|a+b|-1] == a + b[..|b|-1];
      assert (a+b)[|a+b|-1] == b[|b|-1];
      //JournalRangeConcatAssoc(concatFold(a), concatFold(b[..|b|-1]), b[|b|-1].value);
      calc {
        concatFold(a + b);
        concatFold((a + b)[..|a+b|-1]) + [(a+b)[|a+b|-1].value];
        concatFold(a + b[..|b|-1]) + [b[|b|-1].value];
        concatFold(a) + concatFold(b[..|b|-1]) + [b[|b|-1].value];
        concatFold(a) + concatFold(b);
      }
    }
  }


  protected predicate Disk_HasJournalRange(journal: seq<Option<JournalBlock>>, interval: JournalInterval)
  requires ValidJournalInterval(interval)
  {
    && |journal| == NumJournalBlocks() as int
    && var slice := CyclicSlice(journal, interval);
    && fullRange(slice)
  }

  protected function Disk_JournalRange(journal: seq<Option<JournalBlock>>, interval: JournalInterval) : JournalRange
  requires ValidJournalInterval(interval)
  requires Disk_HasJournalRange(journal, interval)
  {
    var slice := CyclicSlice(journal, interval);
    concatFold(slice)
  }

  protected predicate Disk_HasJournal(
      journal: seq<Option<JournalBlock>>, interval: JournalInterval)
  requires ValidJournalInterval(interval)
  {
    && Disk_HasJournalRange(journal, interval)
    && parseJournalRange(Disk_JournalRange(journal, interval)).Some?
  }

  protected function Disk_Journal(
      journal: seq<Option<JournalBlock>>, interval: JournalInterval) : seq<JournalEntry>
  requires ValidJournalInterval(interval)
  requires Disk_HasJournal(journal, interval)
  {
    parseJournalRange(Disk_JournalRange(journal, interval)).value
  }

  lemma Disk_Journal_empty(
      journal: seq<Option<JournalBlock>>, start: int)
  requires ValidJournalInterval(JournalInterval(start, 0))
  requires |journal| == NumJournalBlocks() as int
  ensures Disk_HasJournal(journal, JournalInterval(start, 0))
  ensures Disk_Journal(journal, JournalInterval(start, 0)) == []
  {
    reveal_CyclicSlice();
    parseJournalRangeEmpty();
  }

  function Endpoint(interval: JournalInterval) : int
  {
    if interval.start + interval.len <= NumJournalBlocks() as int then
      interval.start + interval.len
    else
      interval.start + interval.len - NumJournalBlocks() as int
  }

  function concatIntervals(a: JournalInterval, b: JournalInterval) : JournalInterval
  requires Endpoint(a) == b.start
  {
    JournalInterval(a.start, a.len + b.len)
  }

  lemma Disk_Journal_preserves(
      journal: seq<Option<JournalBlock>>,
      journal': seq<Option<JournalBlock>>,
      interval: JournalInterval,
      interval_write: JournalInterval,
      jr: JournalRange)
  requires ValidJournalInterval(interval)
  requires ValidJournalInterval(interval_write)
  requires JournalUpdate(journal, journal', interval_write, jr)
  requires Disk_HasJournal(journal, interval)
  requires !journalCyclicIntervalOverlap(interval, interval_write)

  ensures Disk_HasJournal(journal', interval)
  ensures Disk_Journal(journal, interval)
      == Disk_Journal(journal', interval)
  {
    var c1 := CyclicSlice(journal, interval);
    var c2 := CyclicSlice(journal', interval);

    assert c1 == c2 by {
      reveal_CyclicSlice();
      reveal_JournalUpdate();
    }
  }

  lemma Disk_Journal_append(
      journal: seq<Option<JournalBlock>>,
      journal': seq<Option<JournalBlock>>,
      interval: JournalInterval,
      interval_write: JournalInterval,
      jr: JournalRange)
  requires ValidJournalInterval(interval)
  requires JournalUpdate(journal, journal', interval_write, jr)
  requires Disk_HasJournal(journal, interval)
  requires parseJournalRange(jr).Some?
  requires interval.len + |jr| <= NumJournalBlocks() as int
  requires interval_write.start == Endpoint(interval)
  ensures Disk_HasJournal(journal', concatIntervals(interval, interval_write))
  ensures Disk_Journal(journal', concatIntervals(interval, interval_write))
      == Disk_Journal(journal, interval) + parseJournalRange(jr).value
  {
    var interval' := concatIntervals(interval, interval_write);

    var slice := CyclicSlice(journal, interval);
    var slice' := CyclicSlice(journal', interval');

    forall i | 0 <= i < |slice'|
    ensures slice'[i].Some?
    {
      reveal_CyclicSlice();
      reveal_JournalUpdate();
      if i < interval.len {
        if interval.start + i < NumJournalBlocks() as int {
          calc {
            slice[i];
            journal[i + interval.start];
            journal'[i + interval.start];
            slice'[i];
          }
        } else {
          calc {
            slice[i];
            slice'[i];
          }
        }
        assert slice'[i].Some?;
      } else {
        assert slice'[i].Some?;
      }
    }

    assert fullRange(slice');

    var a := concatFold(slice');
    var b := concatFold(slice) + jr;

    assert |a| == |b| by { reveal_CyclicSlice(); }

    forall i | 0 <= i < |a|
    ensures a[i] == b[i]
    {
      reveal_CyclicSlice();
      reveal_JournalUpdate();
      if i < interval.len {
        if interval.start + i < NumJournalBlocks() as int {
          calc {
            slice[i];
            journal[i + interval.start];
            journal'[i + interval.start];
            slice'[i];
          }
        } else {
          calc {
            slice[i];
            slice'[i];
          }
        }
      } else {
      }
    }

    assert Disk_HasJournalRange(journal', concatIntervals(interval, interval_write));
    assert Disk_JournalRange(journal', concatIntervals(interval, interval_write))
      == Disk_JournalRange(journal, interval) + jr;
    parseJournalRangeAdditive(Disk_JournalRange(journal, interval), jr);
  }

  lemma Disk_Journal_Read(
      journal: seq<Option<JournalBlock>>,
      interval: JournalInterval)
  requires ContiguousJournalInterval(interval)
  requires Disk_HasJournalRange(journal, interval)
  requires parseJournalRange(Disk_JournalRange(journal, interval)).Some?
  ensures Disk_HasJournal(journal, interval)
  ensures Disk_Journal(journal, interval)
      == parseJournalRange(Disk_JournalRange(journal, interval)).value
  {
  }

  lemma Disk_Journal_Read2(
      journal: seq<Option<JournalBlock>>,
      interval: JournalInterval)
  requires ValidJournalInterval(interval)
  requires interval.start + interval.len > NumJournalBlocks() as int
  requires Disk_HasJournalRange(journal, JournalFrontInterval(interval.start, interval.len).value)
  requires Disk_HasJournalRange(journal, JournalBackInterval(interval.start, interval.len).value)
  requires parseJournalRange(Disk_JournalRange(journal, JournalFrontInterval(interval.start, interval.len).value)
                         + Disk_JournalRange(journal, JournalBackInterval(interval.start, interval.len).value)).Some?
  ensures Disk_HasJournal(journal, interval)
  ensures Disk_Journal(journal, interval)
      == parseJournalRange(Disk_JournalRange(journal, JournalFrontInterval(interval.start, interval.len).value)
                         + Disk_JournalRange(journal, JournalBackInterval(interval.start, interval.len).value)).value
  {

    var front := JournalFrontInterval(interval.start, interval.len).value;
    var back := JournalBackInterval(interval.start, interval.len).value;

    assert CyclicSlice(journal, interval)
        == CyclicSlice(journal, front)
          + CyclicSlice(journal, back)
      by { reveal_CyclicSlice(); }

    concatFoldAdditive(
        CyclicSlice(journal, front),
        CyclicSlice(journal, back));
  }

  lemma Disk_Journal_Preserves(
      journal: seq<Option<JournalBlock>>,
      journal': seq<Option<JournalBlock>>,
      interval: JournalInterval)
  requires ValidJournalInterval(interval)
  requires Disk_HasJournal(journal, interval)
  requires |journal| == NumJournalBlocks() as int
  requires |journal'| == NumJournalBlocks() as int
  requires forall i | 0 <= i < NumJournalBlocks() as int
      :: InCyclicRange(i, interval) ==> journal[i] == journal'[i]
  ensures Disk_HasJournal(journal', interval)
  ensures Disk_Journal(journal, interval)
       == Disk_Journal(journal', interval)
  {
    var c1 := CyclicSlice(journal, interval);
    var c2 := CyclicSlice(journal', interval);
    reveal_CyclicSlice();
    assert |c1| == |c2|;
    forall i | 0 <= i < |c1|
    ensures c1[i] == c2[i]
    {
    }
    assert c1 == c2;
  }
}
