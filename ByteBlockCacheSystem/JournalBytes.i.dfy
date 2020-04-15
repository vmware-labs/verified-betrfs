include "../BlockCacheSystem/JournalRange.i.dfy"
include "AsyncDiskModel.s.dfy"

module JournalBytes {
  import opened NativeTypes
  import opened JournalRanges`Internal
  import opened Options
  import opened Sequences
  import D = AsyncDisk

  function {:opaque} JournalBlockOfByteSeq(s: seq<byte>): (res: Option<JournalBlock>)
  ensures res.Some? ==> |res.value| == 4064
  {
    if |s| == 4096 && D.ChecksumChecksOut(s) then
      Some(s[32..])
    else
      None
  }

  function {:opaque} JournalRangeOfByteSeq(s: seq<byte>): (res : Option<JournalRange>)
  ensures res.Some? ==> |res.value| * 4096 == |s|
  ensures res.Some? ==> forall i | 0 <= i < |res.value| :: |res.value[i]| == 4064
  {
    if s == [] then
      Some([])
    else if |s| >= 4096 && JournalBlockOfByteSeq(s[0..4096]).Some? then (
      var rest := JournalRangeOfByteSeq(s[4096..]);
      if rest.Some? then (
        Some([JournalBlockOfByteSeq(s[0..4096]).value] + rest.value)
      ) else (
        None
      )
    )
    else (
      None
    )
  }


  lemma JournalRangeOfByteSeqGetI(a: seq<byte>, i: int)
  requires JournalRangeOfByteSeq(a).Some?
  requires 0 <= i
  requires 4096*(i+1) <= |a|
  ensures JournalRangeOfByteSeq(a[4096*i .. 4096*(i+1)]).Some?
  ensures i < JournalRangeLen(JournalRangeOfByteSeq(a).value)
  ensures JournalRangeOfByteSeq(a[4096*i .. 4096*(i+1)]).value
      == JournalBlockGet(JournalRangeOfByteSeq(a).value, i)
  {
    reveal_JournalRangeOfByteSeq();
    if i == 0 {
      var c := a[4096*i .. 4096*(i+1)];
      assert JournalRangeOfByteSeq(c[4096..]) == Some([]);
      assert c[0..4096] == c;
    } else {
      var a' := a[4096..];
      assert a[4096*i .. 4096*(i+1)] == a'[4096*(i-1) .. 4096*i];
      JournalRangeOfByteSeqGetI(a', i-1);
      var rest := JournalRangeOfByteSeq(a');
      assert ([a[32..4096]] + rest.value)[i] == rest.value[i-1];
      //assert JournalRangeOfByteSeq(a[4096*i .. 4096*(i+1)])
      //    == JournalRangeOfByteSeq(a'[4096*(i-1) .. 4096*i]);
    }
  }

  lemma JournalBlockOfJournalRange(a: seq<byte>, i: int)
  requires JournalRangeOfByteSeq(a).Some?
  requires 0 <= 4096*i <= 4096*(i+1) <= |a|
  ensures JournalBlockOfByteSeq(a[4096*i..4096*(i+1)]).Some?
  ensures JournalRangeOfByteSeq(a).value[i]
      == JournalBlockOfByteSeq(a[4096*i..4096*(i+1)]).value
  {
    if i == 0 {
      reveal_JournalRangeOfByteSeq();
    } else {
      var a' := a[4096..];

      assert JournalRangeOfByteSeq(a').Some?
          && JournalRangeOfByteSeq(a').value[i-1]
              == JournalRangeOfByteSeq(a).value[i] by {
        reveal_JournalRangeOfByteSeq();
        var rest := JournalRangeOfByteSeq(a[4096..]);
        var firstblock := JournalBlockOfByteSeq(a[0..4096]).value;
        assert ([firstblock] + rest.value)[i] == rest.value[i-1];
      }

      calc {
        JournalBlockOfByteSeq(a[4096*i..4096*(i+1)]);
        { assert a[4096*i..4096*(i+1)] == a'[4096*(i-1)..4096*i]; }
        JournalBlockOfByteSeq(a'[4096*(i-1)..4096*i]);
        { JournalBlockOfJournalRange(a', i-1); }
        Some(JournalRangeOfByteSeq(a').value[i-1]);
        Some(JournalRangeOfByteSeq(a).value[i]);
      }
    }
  }

  lemma JournalRangeEqJournalBlocks(a: seq<byte>, t: int)
  requires |a| == t*4096
  requires forall i | 0 <= i < t ::
      JournalBlockOfByteSeq(a[i*4096..(i+1)*4096]).Some?
  ensures JournalRangeOfByteSeq(a).Some?
  ensures forall i | 0 <= i < t ::
      JournalRangeOfByteSeq(a).value[i] == 
          JournalBlockOfByteSeq(a[i*4096..(i+1)*4096]).value
  {
    if t == 0 {
      reveal_JournalRangeOfByteSeq();
    } else {
      reveal_JournalRangeOfByteSeq();
      var a' := a[4096..];

      forall i | 0 <= i < t-1 
      ensures JournalBlockOfByteSeq(a'[i*4096..(i+1)*4096]).Some?
      {
        assert a'[i*4096..(i+1)*4096] == a[(i+1)*4096..(i+2)*4096];
      }

      JournalRangeEqJournalBlocks(a', t-1);
      assert JournalBlockOfByteSeq(a[0*4096..(0+1)*4096]).Some?;
      assert JournalRangeOfByteSeq(a).Some?;

      forall i | 0 <= i < t
      ensures JournalRangeOfByteSeq(a).value[i] == 
          JournalBlockOfByteSeq(a[i*4096..(i+1)*4096]).value
      {
        if i > 0 { 
          calc {
            JournalRangeOfByteSeq(a).value[i];
            JournalRangeOfByteSeq(a').value[i-1];
            JournalBlockOfByteSeq(a'[(i-1)*4096..i*4096]).value;
            {
              assert a'[(i-1)*4096..i*4096]
                  == a[i*4096..(i+1)*4096];
            }
            JournalBlockOfByteSeq(a[i*4096..(i+1)*4096]).value;
          }
        }
      }
    }
  }

  lemma JournalRangeOfJournalBlocks(a: seq<byte>, t: int)
  requires |a| == t*4096
  requires forall i | 0 <= i < t ::
      JournalBlockOfByteSeq(a[i*4096..(i+1)*4096]).Some?
  ensures JournalRangeOfByteSeq(a).Some?
  {
    JournalRangeEqJournalBlocks(a, t);
  }

  lemma JournalRangeOfByteSeqAdditive(a: seq<byte>, b: seq<byte>)
  requires JournalRangeOfByteSeq(a).Some?
  requires JournalRangeOfByteSeq(b).Some?
  ensures JournalRangeOfByteSeq(a + b).Some?
  ensures JournalRangeOfByteSeq(a + b).value
        == JournalRangeOfByteSeq(a).value
         + JournalRangeOfByteSeq(b).value
  {
    var c := a + b;
    var ta := |a| / 4096;
    var tb := |b| / 4096;
    forall i | 0 <= i < ta + tb
    ensures JournalBlockOfByteSeq(c[i*4096..(i+1)*4096]).Some?
    {
      if i < ta {
        assert c[i*4096..(i+1)*4096] == a[i*4096..(i+1)*4096];
        JournalBlockOfJournalRange(a, i);
      } else {
        calc {
          c[i*4096..(i+1)*4096];
          { sum_slice_second(a, b, i*4096, (i+1)*4096); }
          b[(i-ta)*4096..(i-ta+1)*4096];
        }
        JournalBlockOfJournalRange(b, i-ta);
      }
    }

    JournalRangeEqJournalBlocks(c, ta + tb);

    var x := JournalRangeOfByteSeq(a).value;
    var y := JournalRangeOfByteSeq(b).value;
    var z' := x+y;
    var z := JournalRangeOfByteSeq(a + b).value;
    forall i | 0 <= i < |z| ensures z[i] == z'[i]
    {
      if i < ta {
        calc {
          z[i];
          JournalBlockOfByteSeq(c[i*4096..(i+1)*4096]).value;
          { assert c[i*4096..(i+1)*4096] == a[i*4096..(i+1)*4096]; }
          JournalBlockOfByteSeq(a[i*4096..(i+1)*4096]).value;
          { JournalBlockOfJournalRange(a, i); }
          x[i];
          z'[i];
        }
      } else {
        calc {
          z[i];
          JournalBlockOfByteSeq(c[i*4096..(i+1)*4096]).value;
          {
            sum_slice_second(a, b, i*4096, (i+1)*4096);
            assert c[i*4096..(i+1)*4096]
                == b[(i-ta)*4096..(i-ta+1)*4096];
          }
          JournalBlockOfByteSeq(b[(i-ta)*4096..(i-ta+1)*4096]).value;
          { JournalBlockOfJournalRange(b, i-ta); }
          y[i-ta];
          z'[i];
        }
      }
    }
    assert z == z';
  }

  lemma JournalBytesSplit(a: seq<byte>, numBlocks: int, split: int)
  requires JournalRangeOfByteSeq(a).Some?
  requires |JournalRangeOfByteSeq(a).value| == numBlocks
  requires 0 <= split <= numBlocks
  ensures JournalRangeOfByteSeq(a[.. split*4096]).Some?
  ensures JournalRangeOfByteSeq(a[split*4096 ..]).Some?
  ensures JournalRangeOfByteSeq(a).value
    == JournalRangeOfByteSeq(a[.. split*4096]).value
     + JournalRangeOfByteSeq(a[split*4096 ..]).value
  {
    assert JournalRangeOfByteSeq(a[.. split*4096]).Some?
    by {
      var a' := a[.. split*4096];
      forall i | 0 <= i < split
      ensures JournalBlockOfByteSeq(a'[i*4096..(i+1)*4096]).Some?
      {
        assert a'[i*4096..(i+1)*4096]
            == a[i*4096..(i+1)*4096];
        JournalBlockOfJournalRange(a, i);
      }
      JournalRangeOfJournalBlocks(a', split);
    }
    assert JournalRangeOfByteSeq(a[split*4096..]).Some?
    by {
      var a' := a[split*4096..];
      forall i | 0 <= i < numBlocks-split
      ensures JournalBlockOfByteSeq(a'[i*4096..(i+1)*4096]).Some?
      {
        assert a'[i*4096..(i+1)*4096]
            == a[(split+i)*4096..(split+i+1)*4096];
        JournalBlockOfJournalRange(a, split+i);
      }
      JournalRangeOfJournalBlocks(a', numBlocks-split);
    }
    JournalRangeOfByteSeqAdditive(
        a[.. split*4096],
        a[split*4096..]);
    assert a[.. split*4096] + a[split*4096..] == a;
  }
}
