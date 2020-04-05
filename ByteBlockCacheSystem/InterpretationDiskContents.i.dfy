include "InterpretationDiskOps.i.dfy"

module InterpretationDiskContents {
  import InterpretationDiskOps
  import opened AsyncDisk
  import opened NativeTypes
  import opened Maps

  ///// Basic disk interpretation where we imagine all the pending
  ///// writes are already written.

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

  /*lemma onApplyWrite(s: seq<byte>, reqs: map<ReqId, ReqWrite>, id: ReqId)
  requires id in reqs
  requires forall id1, id2 | id1 in reqs && id2 in reqs && id1 != id2
      :: !reqWritesOverlap(reqs[id1], reqs[id2])
  requires 0 <= reqs[id].addr
  requires reqs[id].addr as int + |reqs[id].bytes| <= |s|
  ensures withWrites(s, reqs)
      == withWrites(
            splice(s, reqs[id].addr as int, reqs[id].bytes),
            MapRemove1(reqs, id))
  {
    var a := withWrites(s, reqs);
    var b := withWrites(
        splice(s, reqs[id].addr as int, reqs[id].bytes),
        MapRemove1(reqs, id));
    assert |a| == |b| by { reveal_splice(); }

    forall i | 0 <= i < |a|
    ensures a[i] == b[i]
    {
      if Covers(reqs[id], i) {
        calc {
          a[i];
          reqs[id].bytes[i - reqs[id].addr as int];
          { reveal_splice(); }
          splice(s, reqs[id].addr as int, reqs[id].bytes)[i];
          b[i];
        }
      } else {
        if hasCoveringReqId(reqs, i) {
          var req' := getCoveringReq(reqs, i);
          assert req' == getCoveringReq(MapRemove1(reqs, id), i);
          calc {
            a[i];
            req'.bytes[i - req'.addr as int];
            b[i];
          }
        } else {
          calc {
            a[i];
            s[i];
            { reveal_splice(); }
            splice(s, reqs[id].addr as int, reqs[id].bytes)[i];
            b[i];
          }
        }
      }
    }
  }

  lemma onNewWrite(s: seq<byte>, reqs: map<ReqId, ReqWrite>, id: ReqId, req: ReqWrite)
  requires id !in reqs
  requires forall id1, id2 | id1 in reqs && id2 in reqs && id1 != id2
      :: !reqWritesOverlap(reqs[id1], reqs[id2])
  requires forall id1 | id1 in reqs
      :: !reqWritesOverlap(reqs[id1], req)
  requires 0 <= req.addr
  requires req.addr as int + |req.bytes| <= |s|
  ensures withWrites(s, reqs[id := req])
      == splice(withWrites(s, reqs), req.addr as int, req.bytes)
  {
    var a := withWrites(s, reqs[id := req]);
    var b := splice(withWrites(s, reqs), req.addr as int, req.bytes);

    assert |a| == |b| by { reveal_splice(); }

    forall i | 0 <= i < |a|
    ensures a[i] == b[i]
    {
      if Covers(req, i) {
        assert Covers(reqs[id := req][id], i);
        assert hasCoveringReqId(reqs[id := req], i);
        assert getCoveringReq(reqs[id := req], i) == req;
        calc {
          a[i];
          req.bytes[i - req.addr as int];
          { reveal_splice(); }
          b[i];
        }
      } else {
        if hasCoveringReqId(reqs, i) {
          var id' := getCoveringReqId(reqs, i);
          var req' := getCoveringReq(reqs, i);
          assert Covers(reqs[id := req][id'], i);
          assert req' == getCoveringReq(reqs[id := req], i);
          calc {
            a[i];
            req'.bytes[i - req'.addr as int];
            { reveal_splice(); }
            b[i];
          }
        } else {
          calc {
            a[i];
            s[i];
            { reveal_splice(); }
            b[i];
          }
        }
      }
    }

    assert a == b;
  }

  lemma onSplice(s: seq<byte>, reqs: map<ReqId, ReqWrite>, id: ReqId, req: ReqWrite)
  requires id !in reqs
  requires forall id1, id2 | id1 in reqs && id2 in reqs && id1 != id2
      :: !reqWritesOverlap(reqs[id1], reqs[id2])
  requires forall id1 | id1 in reqs
      :: !reqWritesOverlap(reqs[id1], req)
  requires 0 <= req.addr
  requires req.addr as int + |req.bytes| <= |s|
  ensures splice(withWrites(s, reqs), req.addr as int, req.bytes)
      == withWrites(splice(s, req.addr as int, req.bytes), reqs)
  {
    calc {
      splice(withWrites(s, reqs), req.addr as int, req.bytes);
      { onNewWrite(s, reqs, id, req); }
      withWrites(s, reqs[id := req]);
      { onApplyWrite(s, reqs[id := req], id); }
      withWrites(
          splice(s, reqs[id := req][id].addr as int, reqs[id := req][id].bytes),
          MapRemove1(reqs[id := req], id));
      {
        assert MapRemove1(reqs[id := req], id) == reqs;
        assert reqs[id := req][id] == req;
      }
      withWrites(splice(s, req.addr as int, req.bytes), reqs);
    }
  }*/
}
