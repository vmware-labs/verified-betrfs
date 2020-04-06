include "InterpretationDiskOps.i.dfy"

module InterpretationDiskContents {
  import InterpretationDiskOps
  import opened AsyncDisk
  import opened NativeTypes
  import opened Maps
  import DiskLayout

  ///// Basic disk interpretation where we imagine all the pending
  ///// writes are already written.

  predicate locInBounds(loc: DiskLayout.Location, contents: seq<byte>)
  {
    && loc.addr as int + loc.len as int <= |contents|
  }

  function {:opaque} atLoc(loc: DiskLayout.Location, contents: seq<byte>) : (res : seq<byte>)
  requires locInBounds(loc, contents)
  ensures |res| == loc.len as int
  {
    contents[loc.addr .. loc.addr as int + loc.len as int]
  }

  function atLocWithWrites(loc: DiskLayout.Location, contents: seq<byte>, reqs: map<ReqId, ReqWrite>) : seq<byte>
  {
    withWrites(contents, reqs, loc.addr as int, loc.len as int)
  }

  predicate Covers(req: ReqWrite, i: int)
  {
    req.addr as int <= i < req.addr as int + |req.bytes|
  }

  predicate hasCoveringReqId(
      reqs: map<ReqId, ReqWrite>, i: int)
  {
    exists id :: id in reqs && Covers(reqs[id], i)
  }

  function getCoveringReqId(
      reqs: map<ReqId, ReqWrite>, i: int) : ReqId
  requires hasCoveringReqId(reqs, i)
  {
    var id :| id in reqs && Covers(reqs[id], i);
    id
  }

  function getCoveringReq(
      reqs: map<ReqId, ReqWrite>, i: int) : ReqWrite
  requires hasCoveringReqId(reqs, i)
  {
    reqs[getCoveringReqId(reqs, i)]
  }

  function byteWithWrites(
      s: seq<byte>, reqs: map<ReqId, ReqWrite>, i: int) : byte
  {
    if hasCoveringReqId(reqs, i) then
      var req := getCoveringReq(reqs, i);
      req.bytes[i - req.addr as int]
    else if 0 <= i < |s| then
      s[i]
    else
      0
  }

  function {:opaque} withWritesI(s: seq<byte>, reqs: map<ReqId, ReqWrite>, a: int, len: int)
    : (res: seq<byte>)
  requires len >= 0
  ensures |res| == len
  ensures forall i | 0 <= i < len :: res[i] == byteWithWrites(s, reqs, a + i)
  {
    if len == 0 then [] else
      withWritesI(s, reqs, a, len-1) + [byteWithWrites(s, reqs, a+len-1)]
  }

  protected function withWrites(s: seq<byte>, reqs: map<ReqId, ReqWrite>, a: int, len: int)
    : (res: seq<byte>)
  requires len >= 0
  ensures |res| == len
  {
    withWritesI(s, reqs, a, len)
  }

  predicate reqWritesOverlap(req1: ReqWrite, req2: ReqWrite)
  {
    overlap(req1.addr as int, |req1.bytes|,
        req2.addr as int, |req2.bytes|)
  }

  lemma getReqWriteSelf(s: seq<byte>, reqs: map<ReqId, ReqWrite>, id: ReqId)
  requires id in reqs
  requires forall id1, id2 | id1 in reqs && id2 in reqs && id1 != id2
      :: !reqWritesOverlap(reqs[id1], reqs[id2])
  ensures withWrites(s, reqs, reqs[id].addr as int, |reqs[id].bytes|)
      == reqs[id].bytes
  {
  }

  lemma getReqWriteSelfSub(s: seq<byte>, reqs: map<ReqId, ReqWrite>, id: ReqId, offset: int, len: int)
  requires id in reqs
  requires forall id1, id2 | id1 in reqs && id2 in reqs && id1 != id2
      :: !reqWritesOverlap(reqs[id1], reqs[id2])
  requires 0 <= offset <= offset + len <= |reqs[id].bytes|
  ensures withWrites(s, reqs, reqs[id].addr as int + offset, len)
      == reqs[id].bytes[offset .. offset + len]
  {
  }


  lemma newReqWritePreserve(
    s: seq<byte>, reqs: map<ReqId, ReqWrite>,
    id: ReqId, req: ReqWrite,
    a: int, len: int)
  requires id !in reqs
  requires forall id1, id2 | id1 in reqs && id2 in reqs && id1 != id2
      :: !reqWritesOverlap(reqs[id1], reqs[id2])
  requires req.addr as int >= a + len
        || req.addr as int + |req.bytes| <= a
  requires len >= 0
  ensures withWrites(s, reqs, a, len)
      == withWrites(s, reqs[id := req], a, len)
  {
    var x := withWrites(s, reqs, a, len);
    var y := withWrites(s, reqs[id := req], a, len);
    assert |x| == |y|;
    forall i | 0 <= i < |x| ensures x[i] == y[i]
    {
      if hasCoveringReqId(reqs, a + i) {
        var id1 := getCoveringReqId(reqs, a+i);
        var req1 := getCoveringReq(reqs, a+i);
        assert id1 in reqs[id := req];
        assert Covers(reqs[id := req][id1], a+i);
        assert req1 == getCoveringReq(reqs[id := req], a+i);
        calc {
          x[i];
          byteWithWrites(s, reqs, a + i);
          byteWithWrites(s, reqs[id := req], a + i);
          y[i];
        }
      } else if 0 <= a + i < |s| {
        calc {
          x[i];
          byteWithWrites(s, reqs, a + i);
          byteWithWrites(s, reqs[id := req], a + i);
          y[i];
        }
      } else {
        assert x[i] == y[i];
      }
    }
  }

  lemma atLoc_eq_atLocWithWrites(contents: seq<byte>, reqWrites: map<ReqId, ReqWrite>, loc: DiskLayout.Location)
  requires locInBounds(loc, contents)
  requires forall id | id in reqWrites ::
      |reqWrites[id].bytes| < 0x1_0000_0000_0000_0000
      && !DiskLayout.overlap(InterpretationDiskOps.LocOfReqWrite(reqWrites[id]), loc)
  ensures atLoc(loc, contents)
      == atLocWithWrites(loc, contents, reqWrites);
  {
    reveal_atLoc();
  }

  lemma onApplyWrite(contents: seq<byte>,
      reqWrites: map<ReqId, ReqWrite>,
      start: int, len: int, id: ReqId)
  requires id in reqWrites
  requires len >= 0
  requires reqWrites[id].addr as int + |reqWrites[id].bytes| <= |contents|
  requires forall id1, id2 | id1 in reqWrites && id2 in reqWrites && id1 != id2
      :: !reqWritesOverlap(reqWrites[id1], reqWrites[id2])
  ensures withWrites(contents, reqWrites, start, len)
      == withWrites(splice(contents,
            reqWrites[id].addr as int,
            reqWrites[id].bytes), 
          MapRemove1(reqWrites, id),
          start, len)
  {
    var contents' := splice(contents,
            reqWrites[id].addr as int,
            reqWrites[id].bytes);
    assert |contents| == |contents'| by { reveal_splice(); }
    var reqWrites' := MapRemove1(reqWrites, id);
    var a := withWrites(contents, reqWrites, start, len);
    var b := withWrites(contents', reqWrites', start, len);
    assert |a| == |b|;
    forall i | 0 <= i < |a| ensures a[i] == b[i]
    {
      if Covers(reqWrites[id], start+i) {
        assert reqWrites[id] == getCoveringReq(reqWrites, start+i);
        assert 0 <= start+i < |contents'|;
        calc {
          a[i];
          byteWithWrites(contents, reqWrites, start + i);
          reqWrites[id].bytes[start+i - reqWrites[id].addr as int];
          { reveal_splice(); }
          contents'[start+i];
          b[i];
        }
      } else {
        if 0 <= start+i < |contents| {
          assert contents[start+i] == contents'[start+i] by { reveal_splice(); }
          calc {
            a[i];
            b[i];
          }
        } else {
          assert a[i] == b[i];
        }
      }
    }
  }

  lemma onCrash(contents: seq<byte>, reqs: map<ReqId, ReqWrite>,
      start: int, len: int)
  requires forall id | id in reqs ::
      || start + len <= reqs[id].addr as int 
      || reqs[id].addr as int + |reqs[id].bytes| <= start
  requires len >= 0
  ensures withWrites(contents, reqs, start, len)
      == withWrites(contents, map[], start, len)
  {
    
  }

  lemma withEmptyWrites(contents: seq<byte>, loc: DiskLayout.Location)
  requires locInBounds(loc, contents)
  ensures atLocWithWrites(loc, contents, map[])
      == atLoc(loc, contents)
  {
    reveal_atLoc();
  }
}
