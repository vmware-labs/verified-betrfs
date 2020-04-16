include "../ByteBlockCacheSystem/JournalBytes.i.dfy"
include "../lib/Base/NativeArrays.s.dfy"

module JournalistParsingImpl {
  import opened NativeTypes
  import opened Journal
  import opened JournalBytes
  import opened JournalRanges`Internal
  import opened Sequences
  import opened Options
  import opened Crypto
  import opened NativePackedInts
  import opened KeyType
  import opened ValueType`Internal
  import NativeArrays

  /*method computeJournalRangeOfByteSeqIter(
    s: seq<byte>, 
    ar: array<JournalBlock>,
    i: uint64)
  modifies ar
  requires 0 <= i < ar.Length
  requires ar.Length * 4096 == |s|
  requires |s| < 0xffff_ffff_ffff_ffff
  ensures ar[i..] == JournalRangeOfByteSeq(s[4096*i..])
  {
    reveal_JournalRangeOfByteSeq();
    if i == ar.Length {
    } else {
      computeJournalRangeOfByteSeqIter(s, ar, i+1);
    }
  }*/

  method computeJournalBlockOfByteSeq(s: seq<byte>, i: uint64)
  returns (jb : Option<JournalBlock>)
  requires |s| < 0xffff_ffff_ffff_ffff
  requires i as int + 4096 <= |s|
  ensures jb == JournalBlockOfByteSeq(s[i .. i + 4096])
  {
    reveal_JournalBlockOfByteSeq();

    lemma_seq_slice_slice(s, i as int, (i+4096) as int, 0, 32);
    assert s[i .. i + 32]
        == s[i .. i + 4096][0 .. 32];

    lemma_seq_slice_slice(s, i as int, (i+4096) as int, 32, 4096);
    assert s[i + 32 .. i + 4096]
        == s[i .. i + 4096][32 .. 4096];

    var chunk := s[i + 32 .. i + 4096];
    D.reveal_ChecksumChecksOut();
    var c := Crc32C(chunk);
    if c == s[i .. i + 32] {
      jb := Some(chunk);
    } else {
      jb := None;
    }
  }

  method computeJournalRangeOfByteSeq(s: seq<byte>)
  returns (res: Option<JournalRange>)
  requires |s| < 0x1_0000_0000_0000_0000
  ensures res == JournalRangeOfByteSeq(s)
  ensures res.Some? ==>
      forall i | 0 <= i < |res.value| :: |res.value[i]| == 4064
  {
    if |s| as uint64 % 4096 != 0 {
      return None;
    }
    var numBlocks := |s| as uint64 / 4096;
    var i := numBlocks;
    var ar := new JournalBlock[numBlocks];

    calc {
      JournalRangeOfByteSeq(s[4096*i..]);
      JournalRangeOfByteSeq([]);
      { reveal_JournalRangeOfByteSeq(); }
      Some([]);
      { assert ar[i..] == []; }
      Some(ar[i..]);
    }

    while i > 0
    invariant 0 <= i <= numBlocks
    invariant JournalRangeOfByteSeq(s[4096*i..]) == Some(ar[i..])
    invariant forall j | i <= j < numBlocks :: |ar[j]| == 4064
    {
      ghost var cur := ar[i..];

      i := i - 1;
      var block := computeJournalBlockOfByteSeq(s, 4096*i);
      assert s[4096*i .. 4096*(i+1)]
          == s[4096*i ..][0..4096];
      assert s[4096*(i+1) .. ]
          == s[4096*i ..][4096..];
      if block.Some? {
        assert |block.value| == 4064
          by { reveal_JournalBlockOfByteSeq(); }
        ar[i] := block.value;

        calc {
          JournalRangeOfByteSeq(s[4096*i..]);
          { reveal_JournalRangeOfByteSeq(); }
          Some([block.value] + cur);
          { assert ar[i..] == [ar[i]] + cur; }
          Some(ar[i..]);
        }
      } else {
        assert JournalRangeOfByteSeq(s) == None by {
          reveal_JournalRangeOfByteSeq();
          if JournalRangeOfByteSeq(s).Some? {
            JournalBytesSplit(s, numBlocks as int, i as int);
            assert false;
          }
        }
        return None;
      }
    }

    assert i == 0;

    res := Some(ar[..]);
  }

  method doConcat(s: seq<JournalBlock>)
  returns (t: seq<byte>)
  requires forall i | 0 <= i < |s| :: |s[i]| == 4064
  requires 4064 * |s| < 0xffff_ffff_ffff_ffff
  ensures t == concatSeq(s)
  {
    var ar := new byte[4064 * |s| as uint64];
    var i: uint64 := 0;

    calc {
      concatSeq(s[..i]);
      concatSeq([]);
      { reveal_concatSeq(); }
      [];
    }

    while i < |s| as uint64
    invariant 0 <= i <= |s| as uint64
    invariant ar[0 .. 4064 * i] == concatSeq(s[..i])
    {
      NativeArrays.CopySeqIntoArray(s[i], 0, ar, i*4064, 4064);

      calc {
        ar[0 .. 4064 * (i+1)];
        ar[0 .. 4064 * i] + s[i];
        concatSeq(s[..i]) + s[i];
        {
          reveal_concatSeq();
          assert DropLast(s[..i+1]) == s[..i];
          assert Last(s[..i+1]) == s[i];
        }
        concatSeq(s[..i+1]);
      }

      i := i + 1;
    }

    assert s[..i] == s;
    t := ar[..];
  }

  method ParseHeader(s: JournalBlock)
  returns (nentries: uint32, nblocks: uint32)
  requires |s| >= 8
  requires |s| < 0x1_0000_0000_0000_0000
  ensures parseHeader(s) == Header(nentries as int, nblocks as int)
  {
    reveal_parseHeader();
    nentries := Unpack_LittleEndian_Uint32(s, 0);
    nblocks := Unpack_LittleEndian_Uint32(s, 4);
  }

  method ParseJournalRangeOfBytes(s: seq<byte>, len: uint64)
  returns (res : Option<seq<JournalEntry>>)
  requires 0 <= 8 <= |s| < 0x1_0000_0000_0000_0000
  requires 0 <= len
  ensures res == parseJournalRangeOfBytes(s, len as int)
  ensures res.Some? ==> |res.value| <= |s|
  {
    var ar := new JournalEntry[len];
    var i := 0;
    var idx := 8;

    while i < len
    invariant 0 <= i <= len
    invariant 0 <= idx as int <= |s|
    invariant ar.Length == len as int
    invariant parseEntries(s, (len-i) as int, idx as int).None? ==>
        && parseEntries(s, len as int, 8).None?
    invariant parseEntries(s, (len-i) as int, idx as int).Some? ==>
        && parseEntries(s, len as int, 8).Some?
        && parseEntries(s, len as int, 8).value
          == ar[..i] + parseEntries(s, (len-i) as int, idx as int).value
    invariant i <= idx
    {
      var idx0 := idx;

      if !(4 <= |s| as uint64 - idx0) {
        return None;
      }

      var idx1 := idx0 + 4;

      var keyLen := Unpack_LittleEndian_Uint32(s, idx0);
      if !(4 + keyLen as uint64 + 4 <= |s| as uint64 - idx
              && keyLen as uint64 <= KeyType.MaxLen())
      {
        return None;
      }
      var key: Key := s[idx1..idx1+keyLen as uint64];
      var idx2 := idx1 + keyLen as uint64;
      var valueLen :=
          Unpack_LittleEndian_Uint32(s, idx2);
      var idx3 := idx2 + 4;
      if !(valueLen as uint64 <= ValueType.MaxLen()
              && valueLen as uint64 <= |s| as uint64 - idx3)
      {
        return None;
      }
      var value: Value := s[idx3..idx3+valueLen as uint64];
      var idx4 := idx3 + valueLen as uint64;

      var je := JournalInsert(key, value);

      ar[i] := je;

      i := i + 1;
      idx := idx4;
    }

    res := Some(ar[..]);

    calc {
      ar[..];
      {
        assert parseEntries(s, (len-i) as int, idx as int).value
            == [];
      }
      ar[..i] + parseEntries(s, (len-i) as int, idx as int).value;
      parseEntries(s, len as int, 8).value;
    }
  }

  method ParseJournalRange(jr: JournalRange)
  returns (res : Option<seq<JournalEntry>>)
  requires forall i | 0 <= i < |jr| :: |jr[i]| == 4064
  requires |jr| <= 0x1_0000_0000
  ensures res.Some? ==> |res.value| <= |jr| * 4064
  ensures res == parseJournalRange(jr)
  {
    if |jr| as uint64 == 0 {
      return Some([]);
    } else {
      var nentries, nblocks := ParseHeader(jr[0]);
      if 0 <= nentries
        && 1 <= nblocks as uint64 <= |jr| as uint64
      {
        lemma_concatSeqLen_ge_elemLen(jr[.. nblocks], 0);
        lemma_concatSeqLen_le_mul(jr[.. nblocks], 4064);
        var c := doConcat(jr[.. nblocks]);
        var p1 := ParseJournalRangeOfBytes(c, nentries as uint64);
        if p1.Some? {
          var p2 := ParseJournalRange(jr[nblocks ..]);
          if p2.Some? {
            return Some(p1.value + p2.value);
          } else {
            return None;
          }
        } else {
          return None;
        }
      } else {
        return None;
      }
    }
  }
}
