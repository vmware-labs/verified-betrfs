include "../MapSpec/Journal.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/PackedInts.s.dfy"

module JournalRanges {
  export Spec provides KeyType, Options, ValueMessage, Journal, JournalBlock, parseJournalRange, JournalRangePrefix, JournalRangeSuffix, JournalBlocks, parseJournalRangeEmpty, parseJournalRangeAdditive, JournalRangeConcatAssoc, JournalRangeConcatEmpty, JournalRangeConcatEmpty', JournalRangePrefixGet, JournalRangeSuffixGet
              reveals JournalRangeParses, JournalBlockGet, JournalRange, JournalRangeConcat, JournalRangeEmpty, JournalRangeLen
  export Internal reveals *

  export extends Spec // Default export-style is Spec

  import opened KeyType 
  import ValueType`Internal
  import opened ValueMessage
  import opened Journal
  import opened Options
  import opened NativeTypes
  import opened NativePackedInts
  import opened Sequences

  type JournalBlock = seq<byte>

  // Range of JournalEntries in a form that can be written
  // as a series of blocks on disk, or an incomplete chunk of
  // such a list.
  type JournalRange = seq<JournalBlock>

  function JournalRangeLen(jr: JournalRange) : (len : int)
  ensures len >= 0
  {
    |jr|
  }

  function JournalRangePrefix(jr: JournalRange, i: int) : JournalRange
  requires 0 <= i <= JournalRangeLen(jr)
  ensures JournalRangeLen(JournalRangePrefix(jr, i)) == i
  {
    jr[..i]
  }

  function JournalRangeSuffix(jr: JournalRange, i: int) : JournalRange
  requires 0 <= i <= JournalRangeLen(jr)
  ensures JournalRangeLen(JournalRangeSuffix(jr, i))
      == JournalRangeLen(jr) - i
  {
    jr[i..]
  }

  function JournalRangeConcat(jr1: JournalRange, jr2: JournalRange) : JournalRange
  {
    jr1 + jr2
  }

  function JournalRangeEmpty() : JournalRange
  {
    []
  }

  function JournalBlocksI(jr: JournalRange, i: int)
      : (res : seq<JournalRange>)
  requires 0 <= i <= |jr|
  ensures |res| == i
  ensures forall j | 0 <= j < i :: res[j] == [jr[j]]
  {
    if i == 0 then [] else
      JournalBlocksI(jr, i-1) + [[jr[i-1]]]
  }

  function JournalBlocks(jr: JournalRange) : (res : seq<JournalRange>)
  ensures |res| == JournalRangeLen(jr)
  {
    JournalBlocksI(jr, |jr|)
  }

  function JournalBlockGet(jr: JournalRange, i: int) : (res : JournalRange)
  requires 0 <= i < JournalRangeLen(jr)
  {
    JournalBlocks(jr)[i]
  }

  ///// Parsing

  datatype Header = Header(ghost nentries: int, ghost nblocks: int)

  function {:opaque} parseHeader(s: JournalBlock) : Header
  requires |s| >= 8
  {
    Header(
      unpack_LittleEndian_Uint32(s[0..4]) as int,
      unpack_LittleEndian_Uint32(s[4..8]) as int
    )
  }

  function parseEntries(s: seq<byte>, len: int, idx: int)
      : Option<seq<JournalEntry>>
  requires 0 <= idx <= |s|
  requires 0 <= len
  decreases len
  {
    if len == 0 then
      Some([])
    else (
      if idx + 4 <= |s| then (
        var keyLen := unpack_LittleEndian_Uint32(s[idx..idx+4]) as int;
        if idx + 4 + keyLen + 4 <= |s| && keyLen <= KeyType.MaxLen() as int then (
          var key: Key := s[idx+4..idx+4+keyLen];
          var valueLen := unpack_LittleEndian_Uint32(s[idx+4+keyLen..idx+4+keyLen+4]) as int;
          if idx + 4 + keyLen + 4 + valueLen <= |s| && valueLen <= ValueType.MaxLen() as int then (
            var value: Value := s[idx+4+keyLen+4 .. idx+4+keyLen+4+valueLen];
            var je := JournalInsert(key, value);

            var rest := parseEntries(s, len-1, idx + 4 + keyLen + 4 + valueLen);
            if rest.Some? then (
              Some([je] + rest.value)
            ) else (
              None
            )
          ) else (
            None
          )
        ) else (
          None
        )
      ) else (
        None
      )
    )
  }

  function parseJournalRangeOfBytes(s: seq<byte>, len: int)
      : Option<seq<JournalEntry>>
  requires |s| >= 8
  requires 0 <= len
  {
    parseEntries(s, len, 8)
  }

  function parseJournalRange(jr: JournalRange) : Option<seq<JournalEntry>>
  {
    if |jr| == 0 then
      Some([])
    else (
      if |jr[0]| >= 8 then (
        var header := parseHeader(jr[0]);
        if 0 <= header.nentries && 1 <= header.nblocks <= |jr| then (
          lemma_concatSeqLen_ge_elemLen(jr[.. header.nblocks], 0);
          var p1 := parseJournalRangeOfBytes(
              concatSeq(jr[.. header.nblocks]),
              header.nentries);
          if p1.Some? then (
            var p2 := parseJournalRange(jr[header.nblocks ..]);
            if p2.Some? then (
              Some(p1.value + p2.value)
            ) else (
              None
            )
          ) else (
            None
          )
        ) else (
          None
        )
      ) else (
        None
      )
    )
  }

  predicate JournalRangeParses(jr: JournalRange, jes: seq<JournalEntry>)
  {
    parseJournalRange(jr) == Some(jes)
  }

  lemma parseJournalRangeEmpty()
  ensures parseJournalRange(JournalRangeEmpty()) == Some([])
  {
  }

  lemma parseJournalRangeAdditive(a: JournalRange, b: JournalRange)
  requires parseJournalRange(a).Some?
  requires parseJournalRange(b).Some?
  ensures parseJournalRange(JournalRangeConcat(a, b)).Some?
  ensures parseJournalRange(JournalRangeConcat(a, b)).value
      == parseJournalRange(a).value + parseJournalRange(b).value
  {
    if |a| == 0 {
      calc {
        Some(parseJournalRange(a).value + parseJournalRange(b).value);
        Some(parseJournalRange([]).value + parseJournalRange(b).value);
        Some([] + parseJournalRange(b).value);
        { assert [] + parseJournalRange(b).value == parseJournalRange(b).value; }
        Some(parseJournalRange(b).value);
        parseJournalRange(b);
        { assert a + b == b; }
        parseJournalRange(a + b);
        parseJournalRange(JournalRangeConcat(a, b));
      }
    } else {
      var header := parseHeader(a[0]);
      lemma_concatSeqLen_ge_elemLen(a[.. header.nblocks], 0);
      var a_p1 := parseJournalRangeOfBytes(
          concatSeq(a[.. header.nblocks]),
          header.nentries);
      var a_p2 := parseJournalRange(a[header.nblocks ..]);

      parseJournalRangeAdditive(a[header.nblocks..], b);

      calc {
        Some(parseJournalRange(a).value + parseJournalRange(b).value);
        Some(a_p1.value + a_p2.value + parseJournalRange(b).value);
        {
          assert a_p1.value + a_p2.value + parseJournalRange(b).value
              == a_p1.value + (a_p2.value + parseJournalRange(b).value);
        }
        Some(a_p1.value + (a_p2.value + parseJournalRange(b).value));
        {
          assert a_p2.value + parseJournalRange(b).value
              == parseJournalRange(a[header.nblocks ..] + b).value;
        }
        Some(a_p1.value + parseJournalRange(a[header.nblocks ..] + b).value);
        {
          assert a[header.nblocks ..] + b
              == (a+b)[header.nblocks ..];
        }
        Some(a_p1.value + parseJournalRange((a+b)[header.nblocks ..]).value);
        {
          var c := a + b;
          var c_header := parseHeader(c[0]);
          lemma_concatSeqLen_ge_elemLen(c[.. c_header.nblocks], 0);
          var c_p1 := parseJournalRangeOfBytes(
              concatSeq(c[.. c_header.nblocks]),
              c_header.nentries);
          var c_p2 := parseJournalRange(c[header.nblocks ..]);

          assert header == c_header;
          assert c[.. c_header.nblocks] == a[.. header.nblocks];
          assert a_p1 == c_p1;
        }
        parseJournalRange(a + b);
        parseJournalRange(JournalRangeConcat(a, b));
      }
    }
  }

  lemma JournalRangeConcatAssoc(a: JournalRange, b: JournalRange, c: JournalRange)
  ensures JournalRangeConcat(JournalRangeConcat(a, b), c)
       == JournalRangeConcat(a, JournalRangeConcat(b, c))
  {
  }

  lemma JournalRangeConcatEmpty(a: JournalRange)
  ensures JournalRangeConcat(a, JournalRangeEmpty()) == a
  {
  }

  lemma JournalRangeConcatEmpty'(a: JournalRange)
  ensures JournalRangeConcat(JournalRangeEmpty(), a) == a
  {
  }

  lemma JournalRangePrefixGet(jr: JournalRange, i: int, j: int)
  requires 0 <= j < i <= JournalRangeLen(jr)
  ensures JournalBlockGet(jr, j)
      == JournalBlockGet(JournalRangePrefix(jr, i), j)
  {
  }

  lemma JournalRangeSuffixGet(jr: JournalRange, i: int, j: int)
  requires 0 <= i <= JournalRangeLen(jr)
  requires 0 <= j < JournalRangeLen(jr) - i
  ensures JournalBlockGet(jr, i + j)
      == JournalBlockGet(JournalRangeSuffix(jr, i), j)
  {
  }

  function method WeightJournalEntryUint64(s: JournalEntry) : uint64
  {
    8 + |s.key| as uint64 + |s.value| as uint64
  }

  function WeightJournalEntry(s: JournalEntry) : int
  {
    8 + |s.key| + |s.value|
  }

  function SumJournalEntries(s: seq<JournalEntry>) : int
  ensures SumJournalEntries(s) >= 0
  {
    if |s| == 0 then
      0
    else
      SumJournalEntries(DropLast(s)) + WeightJournalEntry(Last(s))
  }

  function {:opaque} WeightJournalEntries(s: seq<JournalEntry>) : int
  ensures WeightJournalEntries(s) >= 0
  {
    if |s| == 0 then
      0
    else
      // Account 8 bytes for the header.
      SumJournalEntries(s) + 8
  }

  lemma lenTimes8LeSum(s: seq<JournalEntry>)
  ensures 8 * |s| <= SumJournalEntries(s)
  {
    if |s| > 0 {
      lenTimes8LeSum(s[..|s|-1]);
    }
  }

  lemma lenTimes8LeWeight(s: seq<JournalEntry>)
  ensures 8 * |s| <= WeightJournalEntries(s)
  {
    lenTimes8LeSum(s);
    reveal_WeightJournalEntries();
  }

  lemma SumJournalEntriesSum(a: seq<JournalEntry>, b: seq<JournalEntry>)
  ensures SumJournalEntries(a + b)
      == SumJournalEntries(a) + SumJournalEntries(b)
  {
    if b == [] {
      calc {
        SumJournalEntries(a + b);
        { assert a + b == a; }
        SumJournalEntries(a);
        {
          assert SumJournalEntries(b) == 0;
        }
        SumJournalEntries(a) + SumJournalEntries(b);
      }
    } else {
      calc {
        SumJournalEntries(a + b);
        SumJournalEntries(DropLast(a + b)) + WeightJournalEntry(Last(a + b));
        {
          assert DropLast(a + b) == a + DropLast(b);
          assert Last(a + b) == Last(b);
        }
        SumJournalEntries(a + DropLast(b)) + WeightJournalEntry(Last(b));
        {
          SumJournalEntriesSum(a, DropLast(b));
        }
        SumJournalEntries(a) + SumJournalEntries(DropLast(b)) + WeightJournalEntry(Last(b));
        SumJournalEntries(a) + SumJournalEntries(b);
      }
    }
  }

  lemma WeightJournalEntriesSum(s: seq<JournalEntry>, t: seq<JournalEntry>)
  ensures WeightJournalEntries(s + t)
      <= WeightJournalEntries(s) + WeightJournalEntries(t)
  {
    reveal_WeightJournalEntries();
    SumJournalEntriesSum(s, t);
  }

  lemma JournalEntriesSumPrefix(s: seq<JournalEntry>, i: int)
  requires 0 <= i <= |s|
  ensures SumJournalEntries(s[..i]) <= SumJournalEntries(s)
  {
    if i == |s| {
      assert s[..i] == s;
    } else {
      JournalEntriesSumPrefix(DropLast(s), i);
      assert s[..i] == DropLast(s)[..i];
    }
  }
}
