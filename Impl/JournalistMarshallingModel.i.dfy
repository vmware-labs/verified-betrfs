include "../ByteBlockCacheSystem/JournalBytes.i.dfy"
include "../BlockCacheSystem/DiskLayout.i.dfy"
include "../lib/Base/PackedIntsLib.i.dfy"

module JournalistMarshallingModel {
  import opened JournalRanges`Internal
  import opened JournalBytes
  import opened Journal
  import opened DiskLayout
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import opened Crypto
  import opened NativePackedInts
  import opened PackedIntsLib

  function {:opaque} cyclicSlice<T>(t: seq<T>, start: uint64, l: uint64) : (res: seq<T>)
  requires 0 <= start as int < |t|
  requires 0 <= l as int <= |t|
  ensures |res| == l as int
  {
    if start as int + l as int <= |t| then
      t[start .. start as int + l as int]
    else
      t[start ..] + t[.. start as int + l as int - |t| as int]
  }

  ///// Marshalling

  function {:opaque} withoutChecksums(buf: seq<byte>, numBlocks: uint64) : (res: seq<byte>)
  requires |buf| == 4096 * numBlocks as int
  ensures  |res| == 4064 * numBlocks as int
  {
    if numBlocks == 0 then [] else buf[32..4096] + withoutChecksums(buf[4096..], numBlocks-1)
  }

  lemma withoutChecksumsEq(buf: seq<byte>, numBlocks: uint64, block: uint64, idx: uint64)
  requires |buf| == 4096 * numBlocks as int
  requires 0 <= block < numBlocks
  requires 0 <= idx < 4064
  ensures buf[block as int * 4096 + 32 + idx as int]
      == withoutChecksums(buf, numBlocks)[block as int * 4064 + idx as int]
  {
    reveal_withoutChecksums();
    if block == 0 {
    } else {
      withoutChecksumsEq(buf[4096..], numBlocks-1, block - 1, idx);
    }
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

  function splice_get(a: seq<byte>, i: int, start: int, bytes: seq<byte>) : byte
  requires 0 <= i < |a|
  requires 0 <= start <= start + |bytes| <= |a|
  {
    if start <= i < start + |bytes| then
      bytes[i-start]
    else
      a[i]
  }

  lemma writeOntoResult(buf: seq<byte>, numBlocks: uint64, start: uint64, bytes: seq<byte>)
  requires |buf| == 4096 * numBlocks as int
  requires numBlocks <= NumJournalBlocks()
  requires |bytes| <= 4064
  requires 0 <= start as int <= start as int + |bytes| <= 4064 * numBlocks as int
  ensures withoutChecksums(writeOnto(buf, numBlocks, start, bytes), numBlocks)
        == splice(withoutChecksums(buf, numBlocks), start, bytes)
  {
    var a := withoutChecksums(writeOnto(buf, numBlocks, start, bytes), numBlocks);
    var b := splice(withoutChecksums(buf, numBlocks), start, bytes);
    if |bytes| > 0 {
      assert |a| == |b|;
      forall i | 0 <= i < |a| ensures a[i] == b[i]
      {
        var block_i: int := i / 4064;
        var idx_i: int := i % 4064;
        var block := start / 4064;
        var idx := start % 4064;
        if idx + |bytes| as uint64 <= 4064 {
          calc {
            a[i];
            withoutChecksums(writeOnto(buf, numBlocks, start, bytes), numBlocks)[4064*block_i + idx_i];
              { withoutChecksumsEq(writeOnto(buf, numBlocks, start, bytes), numBlocks, block_i as uint64, idx_i as uint64); }
            writeOnto(buf, numBlocks, start, bytes)[4096*block_i + 32 + idx_i];
              { reveal_writeOnto(); }
            splice(buf, block * 4096 + 32 + idx, bytes)[4096*block_i + 32 + idx_i];
              { reveal_splice(); }
            splice_get(buf, 4096*block_i as int + 32 + idx_i as int, block as int * 4096 + 32 + idx as int, bytes);
              { withoutChecksumsEq(buf, numBlocks, block_i as uint64, idx_i as uint64); }
            splice_get(withoutChecksums(buf, numBlocks), i as int, start as int, bytes);
              { reveal_splice(); }
            splice(withoutChecksums(buf, numBlocks), start, bytes)[i];
            b[i];
          }
        } else {
          var buf1 := splice(buf, block * 4096 + 32 + idx, bytes[.. 4064 - idx]);
          var buf2 := splice(buf1, (block + 1) * 4096 + 32, bytes[4064 - idx ..]);
          if i < start as int || i >= start as int + |bytes| {
            calc {
              a[i];
              withoutChecksums(writeOnto(buf, numBlocks, start, bytes), numBlocks)[4064*block_i + idx_i];
              { withoutChecksumsEq(writeOnto(buf, numBlocks, start, bytes), numBlocks, block_i as uint64, idx_i as uint64); }
              writeOnto(buf, numBlocks, start, bytes)[4096*block_i + 32 + idx_i];
              { reveal_writeOnto(); }
              buf2[4096 * block_i + 32 + idx_i];
              { reveal_splice(); }
              buf1[4096 * block_i + 32 + idx_i];
              { reveal_splice(); }
              buf[4096 * block_i + 32 + idx_i];
              { withoutChecksumsEq(buf, numBlocks, block_i as uint64, idx_i as uint64); }
              withoutChecksums(buf, numBlocks)[i];
              { reveal_splice(); }
              splice(withoutChecksums(buf, numBlocks), start, bytes)[i];
              b[i];
            }
          } else if i < start as int + 4064 - idx as int {
            calc {
              a[i];
              withoutChecksums(writeOnto(buf, numBlocks, start, bytes), numBlocks)[4064*block_i + idx_i];
              { withoutChecksumsEq(writeOnto(buf, numBlocks, start, bytes), numBlocks, block_i as uint64, idx_i as uint64); }
              writeOnto(buf, numBlocks, start, bytes)[4096*block_i + 32 + idx_i];
              { reveal_writeOnto(); }
              buf2[4096 * block_i + 32 + idx_i];
              { reveal_splice(); }
              buf1[4096 * block_i + 32 + idx_i];
              { reveal_splice(); }
              bytes[.. 4064 - idx][4096 * block_i + 32 + idx_i - (block * 4096 + 32 + idx) as int];
              bytes[i - start as int];
              { reveal_splice(); }
              splice(withoutChecksums(buf, numBlocks), start, bytes)[i];
              b[i];
            }
          } else {
            calc {
              a[i];
              withoutChecksums(writeOnto(buf, numBlocks, start, bytes), numBlocks)[4064*block_i + idx_i];
              { withoutChecksumsEq(writeOnto(buf, numBlocks, start, bytes), numBlocks, block_i as uint64, idx_i as uint64); }
              writeOnto(buf, numBlocks, start, bytes)[4096*block_i + 32 + idx_i];
              { reveal_writeOnto(); }
              buf2[4096 * block_i + 32 + idx_i];
              { reveal_splice(); }
              bytes[4064 - idx ..][4096 * block_i + 32 + idx_i - ((block + 1) * 4096 + 32) as int];
              bytes[i - start as int];
              { reveal_splice(); }
              splice(withoutChecksums(buf, numBlocks), start, bytes)[i];
              b[i];
            }
          }
        }
      }
      assert a == b;
    } else {
      assert writeOnto(buf, numBlocks, start, bytes) == buf by { reveal_writeOnto(); }
      assert splice(withoutChecksums(buf, numBlocks), start, bytes)
          == withoutChecksums(buf, numBlocks) by { reveal_splice(); }
    }
  }

  function {:opaque} writeIntOnto(buf: seq<byte>, numBlocks: uint64, idx: uint64, val: uint32) : (buf' : seq<byte>)
  requires |buf| == 4096 * numBlocks as int
  requires numBlocks <= NumJournalBlocks()
  requires 0 <= idx
  requires idx as int + 4 <= numBlocks as int * 4064
  ensures |buf'| == |buf|
  {
    var t := pack_LittleEndian_Uint32(val);
    writeOnto(buf, numBlocks, idx, t)
  }

  predicate writeOntoAgrees(buf: seq<byte>, numBlocks: uint64, start: uint64, bytes: seq<byte>, i: int)
  requires writeOnto.requires(buf, numBlocks, start, bytes)
  requires 0 <= i < start as int
  {
    withoutChecksums(writeOnto(buf, numBlocks, start, bytes), numBlocks)[i] == withoutChecksums(buf, numBlocks)[i]
  }

  lemma writeOntoPreserves(buf: seq<byte>, numBlocks: uint64, start: uint64, bytes: seq<byte>)
  requires writeOnto.requires(buf, numBlocks, start, bytes)
  ensures forall i | 0 <= i < start as int :: writeOntoAgrees(buf, numBlocks, start, bytes, i)
  {
    forall i | 0 <= i < start as int
    ensures writeOntoAgrees(buf, numBlocks, start, bytes, i)
    {
      writeOntoResult(buf, numBlocks, start, bytes);
      reveal_writeOnto();
      reveal_splice();
      calc {
        withoutChecksums(writeOnto(buf, numBlocks, start, bytes), numBlocks)[i];
        withoutChecksums(buf, numBlocks)[i];
      }
    }
  }

  lemma writeOntoPreservesSlice(buf: seq<byte>, numBlocks: uint64, start: uint64, bytes: seq<byte>,
      a: int, b: int)
  requires writeOnto.requires(buf, numBlocks, start, bytes)
  requires 0 <= a <= b <= start as int
  ensures withoutChecksums(buf, numBlocks)[a..b]
      == withoutChecksums(writeOnto(buf, numBlocks, start, bytes), numBlocks)[a..b]
  {
    var x := withoutChecksums(buf, numBlocks)[a..b];
    var y := withoutChecksums(writeOnto(buf, numBlocks, start, bytes), numBlocks)[a..b];
    assert |x| == |y|;
    forall i | 0 <= i < |x| ensures x[i] == y[i];
    {
      calc {
        x[i];
        withoutChecksums(buf, numBlocks)[a + i];
        {
          writeOntoPreserves(buf, numBlocks, start, bytes);
          assert writeOntoAgrees(buf, numBlocks, start, bytes, a+i);
        }
        withoutChecksums(writeOnto(buf, numBlocks, start, bytes), numBlocks)[a + i];
        y[i];
      }
    }
  }

  lemma writeOntoMakesSlice(buf: seq<byte>, numBlocks: uint64, start: uint64, bytes: seq<byte>)
  requires |buf| == 4096 * numBlocks as int
  requires numBlocks <= NumJournalBlocks()
  requires |bytes| <= 4064
  requires 0 <= start as int <= start as int + |bytes| <= 4064 * numBlocks as int
  ensures withoutChecksums(writeOnto(buf, numBlocks, start, bytes), numBlocks)[start .. start as int + |bytes|] == bytes
  {
    writeOntoResult(buf, numBlocks, start, bytes);
    assert splice(withoutChecksums(buf, numBlocks), start, bytes)[start .. start as int + |bytes|] == bytes
      by { reveal_splice(); }
  }


  predicate writeIntOntoAgrees(buf: seq<byte>, numBlocks: uint64, start: uint64, val: uint32, i: int)
  requires writeIntOnto.requires(buf, numBlocks, start, val)
  requires 0 <= i < start as int
  {
    withoutChecksums(writeIntOnto(buf, numBlocks, start, val), numBlocks)[i] == withoutChecksums(buf, numBlocks)[i]
  }

  lemma writeIntOntoPreserves(buf: seq<byte>, numBlocks: uint64, start: uint64, val: uint32)
  requires writeIntOnto.requires(buf, numBlocks, start, val)
  ensures forall i | 0 <= i < start as int :: writeIntOntoAgrees(buf, numBlocks, start, val, i)
  {
    reveal_writeIntOnto();
    var bytes := pack_LittleEndian_Uint32(val);
    writeOntoPreserves(buf, numBlocks, start, bytes);
    forall i | 0 <= i < start as int
    ensures writeIntOntoAgrees(buf, numBlocks, start, val, i)
    {
      assert writeOntoAgrees(buf, numBlocks, start, bytes, i);
    }
  }

  lemma writeIntOntoPreservesSlice(buf: seq<byte>, numBlocks: uint64, start: uint64, val: uint32,
      a: int, b: int)
  requires writeIntOnto.requires(buf, numBlocks, start, val)
  requires 0 <= a <= b <= start as int
  ensures withoutChecksums(buf, numBlocks)[a..b]
      == withoutChecksums(writeIntOnto(buf, numBlocks, start, val), numBlocks)[a..b]
  {
    var x := withoutChecksums(buf, numBlocks)[a..b];
    var y := withoutChecksums(writeIntOnto(buf, numBlocks, start, val), numBlocks)[a..b];
    assert |x| == |y|;
    forall i | 0 <= i < |x| ensures x[i] == y[i];
    {
      calc {
        x[i];
        withoutChecksums(buf, numBlocks)[a + i];
        {
          writeIntOntoPreserves(buf, numBlocks, start, val);
          assert writeIntOntoAgrees(buf, numBlocks, start, val, a+i);
        }
        withoutChecksums(writeIntOnto(buf, numBlocks, start, val), numBlocks)[a + i];
        y[i];
      }
    }
  }

  lemma writeIntOntoMakesSlice(buf: seq<byte>, numBlocks: uint64, start: uint64, val: uint32)
  requires |buf| == 4096 * numBlocks as int
  requires numBlocks <= NumJournalBlocks()
  requires 0 <= start as int <= start as int + 4 <= 4064 * numBlocks as int
  ensures unpack_LittleEndian_Uint32(
      withoutChecksums(writeIntOnto(buf, numBlocks, start, val), numBlocks)
        [start .. start as int + 4]
      ) == val
  {
    var t := pack_LittleEndian_Uint32(val);
    //assert unpack_LittleEndian_Uint32(t) == val by {
    //  reveal_unpack_LittleEndian_Uint32();
    //}
    reveal_writeIntOnto();
    writeOntoMakesSlice(buf, numBlocks, start, t);
  }

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
  {
    var start' := if start+1 == |entries| as uint64 then 0 else start+1;
    assert [entries[start]] + cyclicSlice(entries, start', len-1)
        == cyclicSlice(entries, start, len)
      by { reveal_cyclicSlice(); }
    SumJournalEntriesSum([entries[start]], cyclicSlice(entries, start', len-1));
  }

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
      var idx1 := idx + 4;
      var buf1 := writeOnto(buf0, numBlocks, idx1, entries[start].key);
      var idx2 := idx1 + |entries[start].key| as uint64;
      var buf2 := writeIntOnto(buf1, numBlocks, idx2, |entries[start].value| as uint32);
      var idx3 := idx2 + 4;
      var buf3 := writeOnto(buf2, numBlocks, idx3, entries[start].value);
      var idx4 := idx3 + |entries[start].value| as uint64;
      writeJournalEntries(buf3, numBlocks, idx4, entries, start', len - 1)
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

  predicate {:opaque} hasHeader(buf: seq<byte>, header: Header)
  {
    && |buf| >= 8
    && unpack_LittleEndian_Uint32(buf[0..4]) as int == header.nentries
    && unpack_LittleEndian_Uint32(buf[4..8]) as int == header.nblocks
  }

  predicate hasEntryAt(buf: seq<byte>, entry: JournalEntry, start: int)
  {
    var idx0 := start;
    var idx1 := idx0 + 4;
    var idx2 := idx1 + |entry.key|;
    var idx3 := idx2 + 4;
    var idx4 := idx3 + |entry.value|;
    && 0 <= idx0
    && idx4 <= |buf|
    && unpack_LittleEndian_Uint32(buf[idx0..idx1]) as int == |entry.key|
    && unpack_LittleEndian_Uint32(buf[idx2..idx3]) as int == |entry.value|
    && buf[idx1..idx2] == entry.key
    && buf[idx3..idx4] == entry.value
  }

  predicate hasEntry(buf: seq<byte>, entries: seq<JournalEntry>, i: int)
  requires 0 <= i < |entries|
  {
    hasEntryAt(buf, entries[i], 8 + SumJournalEntries(entries[..i]))
  }

  predicate hasEntries(buf: seq<byte>, entries: seq<JournalEntry>, j: int)
  requires 0 <= j <= |entries|
  {
    forall i | 0 <= i < j :: hasEntry(buf, entries, i)
  }

  predicate hasStuff(buf: seq<byte>, numBlocks: int, 
      entries: seq<JournalEntry>)
  {
    && hasEntries(buf, entries, |entries|)
    && hasHeader(buf, Header(|entries|, numBlocks))
  }

  predicate hasChecksumAt(buf: seq<byte>, i: int)
  requires 0 <= i
  requires |buf| >= 4096 * (i + 1)
  {
    Crc32C(buf[4096*i + 32 .. 4096*i + 4096]) == buf[4096*i .. 4096*i + 32]
  }

  predicate hasChecksums(buf: seq<byte>, numBlocks: int)
  requires |buf| == numBlocks * 4096
  {
    forall i | 0 <= i < numBlocks :: hasChecksumAt(buf, i)
  }

  function add_mod(a: int, b: int, c: int) : int
  {
    if a + b >= c then a + b - c else a + b
  }

  lemma slices_eq(buf: seq<byte>, buf': seq<byte>, t: int, a: int, b: int)
  requires |buf| == |buf'|
  requires 0 <= a <= b <= t <= |buf|
  requires forall i | 0 <= i < t :: buf[i] == buf'[i]
  ensures buf[a..b] == buf'[a..b]
  {
  }

  lemma DropLastCyclicSlice(
      entries: seq<JournalEntry>,
      start: uint64, len: uint64)
  requires 0 <= start as int < |entries|
  requires 0 <= len as int < |entries|
  requires len as int + 1 < 0xffff_ffff_ffff_ffff
  ensures DropLast(cyclicSlice(entries, start, len + 1))
      == cyclicSlice(entries, start, len)
  {
    reveal_cyclicSlice();
  }

  lemma lemma_writeJournalEntries(
      buf: seq<byte>, numBlocks: uint64, idx: uint64,
      entries: seq<JournalEntry>, start: uint64, len: uint64, start': uint64, len': uint64)
  requires |buf| == 4096 * numBlocks as int
  requires numBlocks <= NumJournalBlocks()
  requires 0 <= start as int < |entries|
  requires 0 <= len as int <= |entries|
  requires 0 <= start' as int < |entries|
  requires 0 <= len' as int <= len as int
  requires start' as int == add_mod(start as int, (len - len') as int, |entries|)
  requires |entries| < 0xfff_ffff_ffff_ffff
  requires idx as int + SumJournalEntries(cyclicSlice(entries, start', len')) <= 4064 * numBlocks as int

  requires idx as int == 8 + SumJournalEntries(cyclicSlice(entries, start, len - len'))
  requires hasHeader(withoutChecksums(buf, numBlocks), Header(len as int, numBlocks as int))
  requires hasEntries(withoutChecksums(buf, numBlocks), cyclicSlice(entries, start, len), len as int - len' as int)

  ensures var buf' := writeJournalEntries(buf, numBlocks, idx, entries, start', len');
    && hasHeader(withoutChecksums(buf', numBlocks), Header(len as int, numBlocks as int))
    && hasEntries(withoutChecksums(buf', numBlocks), cyclicSlice(entries, start, len), len as int)

  decreases len'
  {
    if len' == 0 {
      reveal_writeJournalEntries();
      return;
    }

    //var start'' := if start'+1 == |entries| as uint64 then 0 else start'+1;
    lemma_cyclicRange_popFront_Sum(entries, start', len');

    var idx1 := idx + 4;
    var idx2 := idx1 + |entries[start'].key| as uint64;
    var idx3 := idx2 + 4;
    var idx4 := idx3 + |entries[start'].value| as uint64;

    var buf1 := writeIntOnto(buf, numBlocks, idx, |entries[start'].key| as uint32);
    var buf2 := writeOnto(buf1, numBlocks, idx1, entries[start'].key);
    var buf3 := writeIntOnto(buf2, numBlocks, idx2, |entries[start'].value| as uint32);
    var buf4 := writeOnto(buf3, numBlocks, idx3, entries[start'].value);

    forall i | 0 <= i < idx ensures withoutChecksums(buf, numBlocks)[i] == withoutChecksums(buf4, numBlocks)[i]
    {
      calc {
        withoutChecksums(buf, numBlocks)[i];
        {
          writeIntOntoPreserves(buf, numBlocks, idx, |entries[start'].key| as uint32);
          assert writeIntOntoAgrees(buf, numBlocks, idx, |entries[start'].key| as uint32, i as int);
        }
        withoutChecksums(buf1, numBlocks)[i];
        {
          writeOntoPreserves(buf1, numBlocks, idx1, entries[start'].key);
          assert writeOntoAgrees(buf1, numBlocks, idx1, entries[start'].key, i as int);
        }
        withoutChecksums(buf2, numBlocks)[i];
        {
          writeIntOntoPreserves(buf2, numBlocks, idx2, |entries[start'].value| as uint32);
          assert writeIntOntoAgrees(buf2, numBlocks, idx2, |entries[start'].value| as uint32, i as int);
        }
        withoutChecksums(buf3, numBlocks)[i];
        {
          writeOntoPreserves(buf3, numBlocks, idx3, entries[start'].value);
          assert writeOntoAgrees(buf3, numBlocks, idx3, entries[start'].value, i as int);
        }
        withoutChecksums(buf4, numBlocks)[i];
      }
    }

    assert hasHeader(withoutChecksums(buf4, numBlocks), Header(len as int, numBlocks as int))
    by {
      reveal_hasHeader();
      slices_eq(withoutChecksums(buf, numBlocks), withoutChecksums(buf4, numBlocks), idx as int, 0, 4);
      slices_eq(withoutChecksums(buf, numBlocks), withoutChecksums(buf4, numBlocks), idx as int, 4, 8);
    }

    var slice := cyclicSlice(entries, start, len);
    forall i | 0 <= i < len as int - len' as int
    ensures hasEntry(withoutChecksums(buf4, numBlocks), slice, i)
    {
      //reveal_hasEntryAt();
      assert hasEntry(withoutChecksums(buf, numBlocks),
          cyclicSlice(entries, start, len), i);
      var entry := slice[i];
      var idx0': int := 8 + SumJournalEntries(slice[..i]);
      var idx1': int := idx0' + 4;
      var idx2': int := idx1' + |entry.key|;
      var idx3': int := idx2' + 4;
      var idx4': int := idx3' + |entry.value|;
      assert idx4' <= idx as int by {
        assert idx4' == 8 + SumJournalEntries(slice[..i+1]) by {
          assert DropLast(slice[..i+1]) == slice[..i];
          assert Last(slice[..i+1]) == slice[i];
        }
        assert idx as int == 8 + SumJournalEntries(slice[..len-len']) by {
          assert slice[..len-len'] == cyclicSlice(entries, start, len - len') by {
            reveal_cyclicSlice();
          }
        }
        JournalEntriesSumPrefix(slice[..len-len'], i+1);
        assert slice[..len-len'][..i+1] == slice[..i+1];
      }
      assert 0 <= idx0';
      assert idx4' <= |withoutChecksums(buf4, numBlocks)|;
      slices_eq(withoutChecksums(buf, numBlocks), withoutChecksums(buf4, numBlocks), idx as int, idx0', idx1');
      slices_eq(withoutChecksums(buf, numBlocks), withoutChecksums(buf4, numBlocks), idx as int, idx1', idx2');
      slices_eq(withoutChecksums(buf, numBlocks), withoutChecksums(buf4, numBlocks), idx as int, idx2', idx3');
      slices_eq(withoutChecksums(buf, numBlocks), withoutChecksums(buf4, numBlocks), idx as int, idx3', idx4');
      //assert unpack_LittleEndian_Uint32(buf4[idx0'..idx1']) as int == |entry.key|;
      //assert unpack_LittleEndian_Uint32(buf4[idx2'..idx3']) as int == |entry.value|;
      //assert buf4[idx1'..idx2'] == entry.key;
      //assert buf4[idx3'..idx4'] == entry.value;
    }
    assert hasEntry(withoutChecksums(buf4, numBlocks), slice, len as int - len' as int) by {
      var entry := slice[len as int - len' as int];
      assert entry == entries[start'] by { reveal_cyclicSlice(); }
      var b := withoutChecksums(buf4, numBlocks);
      assert idx4 as int <= |b|;
      assert unpack_LittleEndian_Uint32(b[idx..idx1]) as int == |entry.key| by {
        writeIntOntoMakesSlice(buf, numBlocks, idx, |entry.key| as uint32);
        writeOntoPreservesSlice(buf1, numBlocks, idx1, entry.key, idx as int, idx1 as int);
        writeIntOntoPreservesSlice(buf2, numBlocks, idx2, |entry.value| as uint32, idx as int, idx1 as int);
        writeOntoPreservesSlice(buf3, numBlocks, idx3, entry.value, idx as int, idx1 as int);
      }
      assert b[idx1..idx2] == entry.key by {
        writeOntoMakesSlice(buf1, numBlocks, idx1, entry.key);
        writeIntOntoPreservesSlice(buf2, numBlocks, idx2, |entry.value| as uint32, idx1 as int, idx2 as int);
        writeOntoPreservesSlice(buf3, numBlocks, idx3, entry.value, idx1 as int, idx2 as int);
      }
      assert unpack_LittleEndian_Uint32(b[idx2..idx3]) as int == |entry.value| by {
        writeIntOntoMakesSlice(buf2, numBlocks, idx2, |entry.value| as uint32);
        writeOntoPreservesSlice(buf3, numBlocks, idx3, entry.value, idx2 as int, idx3 as int);
      }
      assert b[idx3..idx4] == entry.value by {
        writeOntoMakesSlice(buf3, numBlocks, idx3, entry.value);
      }
      assert slice[..len - len'] == cyclicSlice(entries, start, len - len') by { reveal_cyclicSlice(); }
      assert 8 + SumJournalEntries(slice[..len - len']) == idx as int;
    }
    assert hasEntries(withoutChecksums(buf4, numBlocks), slice, len as int - len' as int + 1);

    assert idx4 as int == 8 + SumJournalEntries(cyclicSlice(entries, start, len - len' + 1)) by {
      DropLastCyclicSlice(entries, start, len - len');
      assert DropLast(cyclicSlice(entries, start, len - len' + 1))
          == cyclicSlice(entries, start, len - len') by { reveal_cyclicSlice(); }
      assert Last(cyclicSlice(entries, start, len - len' + 1))
          == entries[start'] by { reveal_cyclicSlice(); }
    }

    lemma_writeJournalEntries(buf4, numBlocks, idx4, entries, start, len, 
        if start' as int + 1 == |entries| then 0 else start' + 1,
        len' - 1);
    reveal_writeJournalEntries();
  }

  lemma fillInChecksumsPreserves(buf: seq<byte>, numBlocks: uint64, i: uint64)
  requires fillInChecksums.requires(buf, numBlocks, i)
  ensures withoutChecksums(fillInChecksums(buf, numBlocks, i), numBlocks)
      == withoutChecksums(buf, numBlocks)
  decreases numBlocks - i
  {
    reveal_fillInChecksums();
    if i == numBlocks {
    } else {
      var buf1 := splice(buf, 4096*i, Crc32C(buf[4096*i + 32 .. 4096*i + 4096]));
      var c0 := withoutChecksums(buf, numBlocks);
      var c1 := withoutChecksums(buf1, numBlocks);
      assert |c0| == |c1|;
      forall i | 0 <= i < |c0| ensures c0[i] == c1[i]
      {
        var block := i / 4064;
        var idx := i % 4064;
        calc {
          c0[i];
          { withoutChecksumsEq(buf, numBlocks, block as uint64, idx as uint64); }
          buf[block * 4096 + 32 + idx];
          { reveal_splice(); }
          buf1[block * 4096 + 32 + idx];
          { withoutChecksumsEq(buf1, numBlocks, block as uint64, idx as uint64); }
          c1[i];
        }
      }
      fillInChecksumsPreserves(buf1, numBlocks, i+1);
    }
  }

  lemma fillInChecksumsHasChecksums(buf: seq<byte>, numBlocks: uint64, i: uint64)
  requires fillInChecksums.requires(buf, numBlocks, i)
  requires forall j | 0 <= j < i as int :: hasChecksumAt(buf, j)
  ensures hasChecksums(fillInChecksums(buf, numBlocks, i), numBlocks as int)
  decreases numBlocks - i
  {
    reveal_fillInChecksums();
    if i == numBlocks {
    } else {
      var buf1 := splice(buf, 4096*i, Crc32C(buf[4096*i + 32 .. 4096*i + 4096]));

      forall j | 0 <= j < i as int
      ensures hasChecksumAt(buf1, j)
      {
        calc {
          Crc32C(buf1[4096*j + 32 .. 4096*j + 4096]);
            {
              reveal_splice();
              assert buf[4096*j + 32 .. 4096*j + 4096]
                  == buf1[4096*j + 32 .. 4096*j + 4096];
            }
          Crc32C(buf[4096*j + 32 .. 4096*j + 4096]);
            { assert hasChecksumAt(buf, j); }
          buf[4096*j .. 4096*j + 32];
            { reveal_splice(); }
          buf1[4096*j .. 4096*j + 32];
        }
      }

      assert hasChecksumAt(buf1, i as int) by {
        calc {
          buf1[4096*i .. 4096*i + 32];
          splice(buf, 4096*i, Crc32C(buf[4096*i + 32 .. 4096*i + 4096]))[4096*i .. 4096*i + 32];
            { reveal_splice(); }
          Crc32C(buf[4096*i + 32 .. 4096*i + 4096]);
            {
              var t0 := buf[4096*i + 32 .. 4096*i + 4096];
              var t1 := buf1[4096*i + 32 .. 4096*i + 4096];
              assert |t0| == |t1|;
              forall k | 0 <= k < |t0| ensures t0[k] == t1[k]
              {
                calc {
                  t0[k];
                  buf[4096 * i as int + 32 + k];
                  { reveal_splice(); }
                  buf1[4096 * i as int + 32 + k];
                  t1[k];
                }
              }
              assert t0 == t1;
            }
          Crc32C(buf1[4096*i + 32 .. 4096*i + 4096]);
        }
      }

      fillInChecksumsHasChecksums(buf1, numBlocks, i+1);
    }
  }

  lemma journalRangeFromHasChecksums(
      buf: seq<byte>, numBlocks: uint64)
  requires |buf| == numBlocks as int * 4096
  requires hasChecksums(buf, numBlocks as int)
  ensures JournalRangeOfByteSeq(buf).Some?
  ensures concatSeq(JournalRangeOfByteSeq(buf).value)
      == withoutChecksums(buf, numBlocks)
  {
    reveal_JournalRangeOfByteSeq();
    if numBlocks == 0 {
      assert concatSeq(JournalRangeOfByteSeq(buf).value) == []
          by { reveal_concatSeq(); }
      assert withoutChecksums(buf, numBlocks) == []
          by { reveal_withoutChecksums(); }
    } else {
      assert D.ChecksumChecksOut(buf[0..4096]) by {
        reveal_JournalBlockOfByteSeq();
        assert hasChecksumAt(buf, 0);
        D.reveal_ChecksumChecksOut();
      }

      var suffix := buf[4096..];

      forall i | 0 <= i < numBlocks as int - 1
      ensures hasChecksumAt(suffix, i)
      {
        assert suffix[4096*i + 32 .. 4096*i + 4096]
            == buf[4096*(i+1) + 32 .. 4096*(i+1) + 4096];
        assert suffix[4096*i .. 4096*i + 32]
            == buf[4096*(i+1) .. 4096*(i+1) + 32];
        assert hasChecksumAt(buf, i+1);
      }
      assert hasChecksums(suffix, numBlocks as int - 1);

      journalRangeFromHasChecksums(buf[4096..], numBlocks - 1);
      var rest := JournalRangeOfByteSeq(buf[4096..]).value;

      reveal_JournalBlockOfByteSeq();

      calc {
        concatSeq(JournalRangeOfByteSeq(buf).value);
        concatSeq([buf[32..4096]] + rest);
          { concatSeqAdditive([buf[32..4096]], rest); }
        concatSeq([buf[32..4096]]) + concatSeq(rest);
          { reveal_concatSeq(); }
        buf[32..4096] + concatSeq(rest);
          { reveal_withoutChecksums(); }
        withoutChecksums(buf, numBlocks);
      }
    }
  }

  lemma parseHeaderFromHasHeader(buf: seq<byte>, header: Header)
  requires |buf| >= 8
  requires hasHeader(buf, header)
  ensures parseHeader(buf) == header
  {
    reveal_hasHeader();
    reveal_parseHeader();
  }

  lemma parseEntriesFromHasEntriesI(buf: seq<byte>, entries: seq<JournalEntry>, i: int, idx: int)
  requires 0 <= idx <= |buf|
  requires 0 <= i <= |entries|
  requires idx == 8 + SumJournalEntries(entries[..i])
  requires hasEntries(buf, entries, |entries|)
  ensures parseEntries(buf, |entries| - i, idx).Some?
  ensures parseEntries(buf, |entries| - i, idx).value == entries[i..]
  decreases |entries| - i
  {
    if i == |entries| {
    } else {
      assert hasEntry(buf, entries, i);
      var idx' := idx + WeightJournalEntry(entries[i]);
      assert idx' == 8 + SumJournalEntries(entries[..i+1]) by {
        assert DropLast(entries[..i+1]) == entries[..i];
        assert Last(entries[..i+1]) == entries[i];
      }
      parseEntriesFromHasEntriesI(buf, entries, i+1, idx');
      calc {
        parseEntries(buf, |entries| - i, idx).value;
        [entries[i]] + parseEntries(buf, |entries| - i - 1, idx').value;
        [entries[i]] + entries[i+1..];
        entries[i..];
      }
    }
  }

  lemma parseEntriesFromHasEntries(buf: seq<byte>, entries: seq<JournalEntry>)
  requires 8 <= |buf|
  requires hasEntries(buf, entries, |entries|)
  ensures parseEntries(buf, |entries|, 8).Some?
  ensures parseEntries(buf, |entries|, 8).value == entries
  {
    parseEntriesFromHasEntriesI(buf, entries, 0, 8);
    assert entries[0..] == entries;
  }

  lemma parsesFromStuff(buf: seq<byte>, numBlocks: uint64, entries: seq<JournalEntry>)
  requires |buf| == numBlocks as int * 4096
  requires hasStuff(withoutChecksums(buf, numBlocks), numBlocks as int, entries)
  requires hasChecksums(buf, numBlocks as int)

  ensures JournalRangeOfByteSeq(buf).Some?
  ensures parseJournalRange(JournalRangeOfByteSeq(buf).value)
      == Some(entries)
  {
    assert 8 <= |buf| by { reveal_hasHeader(); }

    journalRangeFromHasChecksums(buf, numBlocks);
    parseHeaderFromHasHeader(withoutChecksums(buf, numBlocks), Header(|entries|, numBlocks as int));
    parseEntriesFromHasEntries(withoutChecksums(buf, numBlocks), entries);

    var jr := JournalRangeOfByteSeq(buf).value;
    assert |jr| == numBlocks as int;

    assert |jr[0]| >= 8 by {
      reveal_JournalBlockOfByteSeq();
      reveal_JournalRangeOfByteSeq();
    }
    assert parseHeader(concatSeq(jr)) == parseHeader(jr[0])
    by {
      calc {
        concatSeq(jr);
        { assert jr == [jr[0]] + jr[1..]; }
        concatSeq([jr[0]] + jr[1..]);
        { concatSeqAdditive([jr[0]], jr[1..]); }
        concatSeq([jr[0]]) + concatSeq(jr[1..]);
        {
          reveal_concatSeq();
          assert concatSeq([jr[0]]) == jr[0];
        }
        jr[0] + concatSeq(jr[1..]);
      }
      reveal_parseHeader();
      assert concatSeq(jr)[0..4] == jr[0][0..4];
      assert concatSeq(jr)[4..8] == jr[0][4..8];
    }

    calc {
      parseJournalRange(jr);
        { assert jr[..numBlocks] == jr; }
      Some(entries + parseJournalRange(jr[numBlocks..]).value);
      Some(entries + parseJournalRange([]).value);
      Some(entries + []);
        { assert entries + [] == entries; }
      Some(entries);
    }
  }

  lemma parseOfWriteJournalEntries(buf: seq<byte>, numBlocks: uint64, len: uint64,
      entries: seq<JournalEntry>, start: uint64,
      buf1: seq<byte>, buf2: seq<byte>, buf3: seq<byte>)
  requires 0 <= start as int < |entries|
  requires 0 <= len as int <= |entries|
  requires |entries| <= 0xffff_ffff
  requires 1 <= numBlocks <= NumJournalBlocks()
  requires |buf| == 4096 * numBlocks as int
  requires 8 + SumJournalEntries(cyclicSlice(entries, start, len)) <= 4064 * numBlocks as int
  requires buf1 == writeHeader(buf, numBlocks, len);
  requires buf2 == writeJournalEntries(buf1, numBlocks, 8, entries, start, len);
  requires buf3 == fillInChecksums(buf2, numBlocks, 0);
  ensures JournalRangeOfByteSeq(buf3).Some?
  ensures parseJournalRange(JournalRangeOfByteSeq(buf3).value)
       == Some(cyclicSlice(entries, start, len))
  {
    assert hasHeader(withoutChecksums(buf1, numBlocks),
        Header(len as int, numBlocks as int))
    by {
      var b0 := buf;
      var b1 := writeIntOnto(b0, numBlocks, 0, len as uint32);
      var b2 := writeIntOnto(b1, numBlocks, 4, numBlocks as uint32);

      writeIntOntoMakesSlice(b0, numBlocks, 0, len as uint32);
      writeIntOntoMakesSlice(b1, numBlocks, 4, numBlocks as uint32);
      writeIntOntoPreservesSlice(b1, numBlocks, 4, numBlocks as uint32, 0, 4);
      reveal_hasHeader();
    }

    lemma_writeJournalEntries(buf1, numBlocks, 8, entries, start, len, start, len);
    fillInChecksumsPreserves(buf2, numBlocks, 0);
    fillInChecksumsHasChecksums(buf2, numBlocks, 0);
    parsesFromStuff(buf3, numBlocks, cyclicSlice(entries, start, len));
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
    reveal_WeightJournalEntries();

    var buf := fill((numBlocks * 4096) as int, 0);
    var buf1 := writeHeader(buf, numBlocks, len);
    var buf2 := writeJournalEntries(buf1, numBlocks, 8, entries, start, len);
    var buf3 := fillInChecksums(buf2, numBlocks, 0);

    parseOfWriteJournalEntries(buf, numBlocks, len, entries, start, buf1, buf2, buf3);

    buf3
  }
}
