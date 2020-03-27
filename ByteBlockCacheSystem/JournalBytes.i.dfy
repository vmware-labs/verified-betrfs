include "../BlockCacheSystem/JournalRange.i.dfy"
include "AsyncDiskModel.s.dfy"

module JournalBytes {
  import opened NativeTypes
  import opened JournalRanges`Internal
  import opened Options
  import D = AsyncDisk

  function {:opaque} JournalBlockOfByteSeq(s: seq<byte>): Option<JournalBlock>
  {
    if |s| == 4096 then
      Some(s[32..4096])
    else
      None
  }

  function {:opaque} JournalRangeOfByteSeq(s: seq<byte>): (res : Option<JournalRange>)
  ensures res.Some? ==> |res.value| * 4096 == |s|
  {
    if s == [] then
      Some([])
    else if |s| >= 4096 && D.ChecksumChecksOut(s[0..4096]) then (
      var rest := JournalRangeOfByteSeq(s[4096..]);
      if rest.Some? then (
        Some([s[32..4096]] + rest.value)
      ) else (
        None
      )
    )
    else (
      None
    )
  }

  lemma JournalRangeOfByteSeqAdditive(a: seq<byte>, b: seq<byte>)
  requires JournalRangeOfByteSeq(a).Some?
  requires JournalRangeOfByteSeq(b).Some?
  ensures JournalRangeOfByteSeq(a + b).Some?
  ensures JournalRangeOfByteSeq(a + b).value
        == JournalRangeOfByteSeq(a).value
         + JournalRangeOfByteSeq(b).value

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
}
