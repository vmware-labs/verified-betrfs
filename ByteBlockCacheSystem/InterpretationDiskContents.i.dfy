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
  requires 0 <= i < |s|
  {
    if hasCoveringReqId(reqs, i) then
      var req := getCoveringReq(reqs, i);
      req.bytes[i - req.addr as int]
    else
      s[i]
  }

  function {:opaque} withWritesI(s: seq<byte>, reqs: map<ReqId, ReqWrite>, j: int)
    : (s': seq<byte>)
  requires 0 <= j <= |s|
  ensures |s'| == j
  ensures forall i | 0 <= i < j :: s'[i] == byteWithWrites(s, reqs, i)
  {
    if j == 0 then [] else
      withWritesI(s, reqs, j-1) + [byteWithWrites(s, reqs, j-1)]
  }

  protected function withWrites(s: seq<byte>, reqs: map<ReqId, ReqWrite>)
    : (s': seq<byte>)
  ensures |s'| == |s|
  {
    withWritesI(s, reqs, |s|)
  }

  predicate reqWritesOverlap(req1: ReqWrite, req2: ReqWrite)
  {
    overlap(req1.addr as int, |req1.bytes|,
        req2.addr as int, |req2.bytes|)
  }

  lemma onApplyWrite(s: seq<byte>, reqs: map<ReqId, ReqWrite>, id: ReqId)
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
  }
}
