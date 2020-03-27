include "../ByteBlockCacheSystem/JournalBytes.i.dfy"
include "../BlockCacheSystem/DiskLayout.i.dfy"

module JournalistMarshallingModel {
  import opened JournalRanges`Internal
  import opened JournalBytes
  import opened Journal
  import opened DiskLayout
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import opened Crypto

  function {:opaque} cyclicSlice<T>(t: seq<T>, start: uint64, l: uint64) : (res: seq<T>)
  requires 0 <= start as int < |t|
  requires 0 <= l as int <= |t|
  ensures l == 0 <==> res == []
  {
    if start as int + l as int <= |t| then
      t[start .. start as int + l as int]
    else
      t[start ..] + t[.. start as int + l as int - |t| as int]
  }

  ///// Marshalling

  lemma lemma_concatSeqJournalRangeLen(buf: seq<byte>, numBlocks: uint64)
  requires |buf| == 4096 * numBlocks as int
  ensures JournalRangeOfByteSeq(buf).Some?
  ensures |concatSeq(JournalRangeOfByteSeq(buf).value)| == 4064 * numBlocks as int

  function {:opaque} withoutChecksums(buf: seq<byte>, numBlocks: uint64) : (res: seq<byte>)
  requires |buf| == 4096 * numBlocks as int
  ensures  |res| == 4064 * numBlocks as int
  {
    lemma_concatSeqJournalRangeLen(buf, numBlocks);
    concatSeq(JournalRangeOfByteSeq(buf).value)
  }

  function {:opaque} splice(bytes: seq<byte>, start: uint64, ins: seq<byte>) : (res: seq<byte>)
  requires 0 <= start
  requires start as int + |ins| <= |bytes|
  requires |bytes| < 0x1_0000_0000_0000_0000
  ensures |res| == |bytes|
  {
    bytes[.. start] + ins + bytes[start + |ins| as uint64 ..]
  }

  function {:opaque} writeOnto(buf: seq<byte>, numBlocks: uint64, start: uint64, bytes: seq<byte>)
      : (buf' : seq<byte>)
  requires |buf| == 4096 * numBlocks as int
  requires numBlocks <= NumJournalBlocks()
  requires |bytes| <= 4064
  requires 0 <= start as int <= start as int + |bytes| <= 4064 * numBlocks as int
  ensures |buf'| == |buf|
  {
    if |bytes| as uint64 > 0 then (
      var block := start / 4064;
      var idx := start % 4064;
      assert start == block * 4064 + idx;
      assert block < numBlocks;
      if idx + |bytes| as uint64 <= 4064 then (
        splice(buf, block * 4096 + 32 + idx, bytes)
      ) else (
        var buf1 := splice(buf, block * 4096 + 32 + idx, bytes[.. 4064 - idx]);
        var buf2 := splice(buf1, (block + 1) * 4096 + 32, bytes[4064 - idx ..]);
        buf2
      )
    ) else (
      buf
    )
  }

  lemma writeOntoResult(buf: seq<byte>, numBlocks: uint64, start: uint64, bytes: seq<byte>)
  requires |buf| == 4096 * numBlocks as int
  requires numBlocks <= NumJournalBlocks()
  requires |bytes| <= 4064
  requires 0 <= start as int <= start as int + |bytes| <= 4064 * numBlocks as int
  ensures withoutChecksums(writeOnto(buf, numBlocks, start, bytes), numBlocks)
        == splice(withoutChecksums(buf, numBlocks), start, bytes)

  function writeIntOnto(buf: seq<byte>, numBlocks: uint64, idx: uint64, val: uint32) : (buf' : seq<byte>)
  requires |buf| == 4096 * numBlocks as int
  requires numBlocks <= NumJournalBlocks()
  ensures |buf'| == |buf|

  function writeHeader(buf: seq<byte>, numBlocks: uint64, len: uint64) : (buf' : seq<byte>)
  requires |buf| == 4096 * numBlocks as int
  requires 1 <= numBlocks <= NumJournalBlocks()
  requires len <= 0xffff_ffff
  ensures |buf'| == |buf|
  {
    var buf1 := writeIntOnto(buf, numBlocks, 0, len as uint32);
    var buf2 := writeIntOnto(buf1, numBlocks, 4, numBlocks as uint32);
    buf2
  }

  lemma lemma_cyclicRange_popFront_Sum(entries: seq<JournalEntry>, start: uint64, len: uint64)
  requires |entries| < 0xfff_ffff_ffff_ffff
  requires 0 <= start as int < |entries|
  requires 1 <= len as int <= |entries|
  ensures var start' := if start+1 == |entries| as uint64 then 0 else start+1;
         SumJournalEntries(cyclicSlice(entries, start, len))
      == SumJournalEntries(cyclicSlice(entries, start', len-1))
            + WeightJournalEntry(entries[start]);

  function {:opaque} writeJournalEntries(buf: seq<byte>, numBlocks: uint64, idx: uint64,
      entries: seq<JournalEntry>, start: uint64, len: uint64) : (buf' : seq<byte>)
  requires |buf| == 4096 * numBlocks as int
  requires numBlocks <= NumJournalBlocks()
  requires 0 <= start as int < |entries|
  requires 0 <= len as int <= |entries|
  requires |entries| < 0xfff_ffff_ffff_ffff
  requires idx as int + SumJournalEntries(cyclicSlice(entries, start, len)) <= 4064 * numBlocks as int
  ensures |buf'| == |buf|
  decreases len
  {
    if len == 0 then
      buf
    else (
      var start' := if start+1 == |entries| as uint64 then 0 else start+1;
      lemma_cyclicRange_popFront_Sum(entries, start, len);

      var buf0 := writeIntOnto(buf, numBlocks, idx, |entries[start].key| as uint32);
      var idx0 := idx + 4;
      var buf1 := writeOnto(buf0, numBlocks, idx0, entries[start].key);
      var idx1 := idx0 + |entries[start].key| as uint64;
      var buf2 := writeIntOnto(buf1, numBlocks, idx1, |entries[start].value| as uint32);
      var idx2 := idx1 + 4;
      var buf3 := writeOnto(buf2, numBlocks, idx2, entries[start].value);
      var idx3 := idx2 + |entries[start].value| as uint64;
      writeJournalEntries(buf3, numBlocks, idx3, entries, start', len - 1)
    )
  }

  function {:opaque} fillInChecksums(buf: seq<byte>, numBlocks: uint64, i: uint64) : (buf' : seq<byte>)
  requires |buf| == numBlocks as int * 4096
  requires numBlocks <= NumJournalBlocks()
  requires 0 <= i <= numBlocks
  ensures |buf'| == |buf|
  decreases numBlocks - i
  {
    if i == numBlocks then
      buf
    else (
      var buf1 := splice(buf, 4096*i, Crc32C(buf[4096*i + 32 .. 4096*i + 4096]));
      fillInChecksums(buf1, numBlocks, i+1)
    )
  }

  function {:opaque} marshallJournalEntries(entries: seq<JournalEntry>,
      start: uint64, len: uint64, numBlocks: uint64)
    : (res: seq<byte>)
  requires 0 <= start as int < |entries|
  requires 0 <= len as int <= |entries|
  requires |entries| <= 0xffff_ffff
  requires WeightJournalEntries(cyclicSlice(entries, start, len)) <= 4064 * numBlocks as int
  requires 1 <= numBlocks <= NumJournalBlocks()
  ensures JournalRangeOfByteSeq(res).Some?
  ensures parseJournalRange(JournalRangeOfByteSeq(res).value)
       == Some(cyclicSlice(entries, start, len))
  ensures |res| == numBlocks as int * 4096
  {
    var buf := fill((numBlocks * 4096) as int, 0);
    var buf1 := writeHeader(buf, numBlocks, len);
    var buf2 := writeJournalEntries(buf1, numBlocks, 8, entries, start, len);
    var buf3 := fillInChecksums(buf2, numBlocks, 0);
    buf3
  }
}
