include "DiskLayout.i.dfy"
include "AsyncSectorDiskModel.i.dfy"
include "../lib/Base/sequences.i.dfy"

//
// Interpretation of the journal stored on the disk
// and lemmas thereof. Useful for BlockCacheSystem proofs.
//

module JournalDiskUtils {
  import opened DiskLayout
  import opened NativeTypes
  import opened JournalRanges
  import opened SectorType
  import opened AsyncSectorDisk
  import opened Journal
  import opened Options
  import opened Sequences

  type DiskConstants = AsyncSectorDisk.Constants
  type DiskState = AsyncSectorDisk.Variables

  predicate WFRange(start: int, len: int)
  {
    && 0 <= start < NumJournalBlocks() as int
    && 0 <= len <= NumJournalBlocks() as int
  }

  predicate NoOverlaps(reqWrites: map<ReqId, ReqWrite>)
  {
    forall id1, id2 | id1 in reqWrites && id2 in reqWrites ::
        overlap(reqWrites[id1].loc, reqWrites[id2].loc) ==> id1 == id2
  }

  function Disk_JournalBlockAtLoc(blocks: imap<Location, Sector>, loc: Location)
    : Option<JournalRange>
  {
    if loc in blocks && blocks[loc].SectorJournal? then
      Some(blocks[loc].journal)
    else
      None
  }

  function Disk_JournalBlockAt(blocks: imap<Location, Sector>, i: int)
    : Option<JournalRange>
  requires 0 <= i < NumJournalBlocks() as int
  {
    Disk_JournalBlockAtLoc(blocks, JournalRangeLocation(i as uint64, 1))
  }

  function Queue_JournalBlockAt(reqWrites: map<ReqId, ReqWrite>, i: int)
    : Option<JournalRange>
  requires 0 <= i < NumJournalBlocks() as int
  {
    var loc := JournalRangeLocation(i as uint64, 1);
    if id :| id in reqWrites
        && ValidJournalLocation(reqWrites[id].loc)
        && LocationSub(loc, reqWrites[id].loc) then (
      if reqWrites[id].sector.SectorJournal?
         && 0 <= i - JournalBlockIdx(reqWrites[id].loc) < 
            JournalRangeLen(reqWrites[id].sector.journal) then (
        Some(JournalBlockGet(reqWrites[id].sector.journal,
            i - JournalBlockIdx(reqWrites[id].loc)))
      ) else (
        None
      )
    ) else (
      None
    )
  }

  function DiskQueue_JournalBlockAt(disk: DiskState, i: int)
    : Option<JournalRange>
  requires 0 <= i < NumJournalBlocks() as int
  {
    if Queue_JournalBlockAt(disk.reqWrites, i).Some? then
      Queue_JournalBlockAt(disk.reqWrites, i)
    else
      Disk_JournalBlockAt(disk.blocks, i)
  }

  function Disk_JournalBlockSeq_i(blocks: imap<Location, Sector>, i: int)
    : (res : seq<Option<JournalRange>>)
  requires 0 <= i <= NumJournalBlocks() as int
  ensures |res| == i
  ensures forall j | 0 <= j < i :: res[j] == Disk_JournalBlockAt(blocks, j)
  {
    if i == 0 then [] else
      Disk_JournalBlockSeq_i(blocks, i-1) + [Disk_JournalBlockAt(blocks, i-1)]
  }

  function Disk_JournalBlockSeq(blocks: imap<Location, Sector>)
    : (res : seq<Option<JournalRange>>)
  ensures |res| == NumJournalBlocks() as int
  ensures forall j | 0 <= j < NumJournalBlocks() as int :: res[j] == Disk_JournalBlockAt(blocks, j)
  {
    Disk_JournalBlockSeq_i(blocks, NumJournalBlocks() as int)
  }

  function DiskQueue_JournalBlockSeq_i(disk: DiskState, i: int)
    : (res : seq<Option<JournalRange>>)
  requires 0 <= i <= NumJournalBlocks() as int
  ensures |res| == i
  ensures forall j | 0 <= j < i :: res[j] == DiskQueue_JournalBlockAt(disk, j)
  {
    if i == 0 then [] else
      DiskQueue_JournalBlockSeq_i(disk, i-1) + [DiskQueue_JournalBlockAt(disk, i-1)]
  }

  function DiskQueue_JournalBlockSeq(disk: DiskState)
    : (res : seq<Option<JournalRange>>)
  ensures |res| == NumJournalBlocks() as int
  ensures forall j | 0 <= j < NumJournalBlocks() as int :: res[j] == DiskQueue_JournalBlockAt(disk, j)
  {
    DiskQueue_JournalBlockSeq_i(disk, NumJournalBlocks() as int)
  }

  function CyclicSlice<T>(s: seq<T>, start: int, len: int) : seq<T>
  requires |s| == NumJournalBlocks() as int
  requires 0 <= start < NumJournalBlocks() as int
  requires 0 <= len <= NumJournalBlocks() as int
  {
    if start + len <= NumJournalBlocks() as int then
      s[start .. start + len]
    else
      s[start ..] + s[.. start + len - NumJournalBlocks() as int]
  }

  predicate fullRange(s: seq<Option<JournalRange>>)
  {
    forall i | 0 <= i < |s| :: s[i].Some?
  }

  function concatFold(s: seq<Option<JournalRange>>) : JournalRange
  requires fullRange(s)
  {
    if s == [] then JournalRangeEmpty() else
      JournalRangeConcat(concatFold(DropLast(s)), Last(s).value)
  }

  predicate Disk_HasJournalRange(
      blocks: imap<Location, Sector>, start: int, len: int)
  requires WFRange(start, len)
  {
    && var slice := CyclicSlice(Disk_JournalBlockSeq(blocks), start, len);
    && fullRange(slice)
  }

  function Disk_JournalRange(blocks: imap<Location, Sector>, start: int, len: int) : JournalRange
  requires WFRange(start, len)
  requires Disk_HasJournalRange(blocks, start, len)
  {
    var slice := CyclicSlice(Disk_JournalBlockSeq(blocks), start, len);
    concatFold(slice)
  }

  protected predicate Disk_HasJournal(
      blocks: imap<Location, Sector>, start: int, len: int)
  requires WFRange(start, len)
  {
    && Disk_HasJournalRange(blocks, start, len)
    && parseJournalRange(Disk_JournalRange(blocks, start, len)).Some?
  }

  protected function Disk_Journal(
      blocks: imap<Location, Sector>, start: int, len: int) : seq<JournalEntry>
  requires WFRange(start, len)
  requires Disk_HasJournal(blocks, start, len)
  {
    parseJournalRange(Disk_JournalRange(blocks, start, len)).value
  }

  predicate DiskQueue_HasJournalRange(
      disk: DiskState, start: int, len: int)
  requires WFRange(start, len)
  {
    && NoOverlaps(disk.reqWrites)
    && var slice := CyclicSlice(DiskQueue_JournalBlockSeq(disk), start, len);
    && fullRange(slice)
  }

  function DiskQueue_JournalRange(
      disk: DiskState, start: int, len: int) : JournalRange
  requires WFRange(start, len)
  requires DiskQueue_HasJournalRange(disk, start, len)
  {
    var slice := CyclicSlice(DiskQueue_JournalBlockSeq(disk), start, len);
    concatFold(slice)
  }

  protected predicate DiskQueue_HasJournal(
      disk: DiskState, start: int, len: int)
  requires WFRange(start, len)
  {
    && DiskQueue_HasJournalRange(disk, start, len)
    && parseJournalRange(DiskQueue_JournalRange(disk, start, len)).Some?
  }

  protected function DiskQueue_Journal(
      disk: DiskState, start: int, len: int) : seq<JournalEntry>
  requires WFRange(start, len)
  requires DiskQueue_HasJournal(disk, start, len)
  {
    parseJournalRange(DiskQueue_JournalRange(disk, start, len)).value
  }

  lemma Disk_eq_DiskQueue(disk: DiskState, start: int, len: int)
  requires WFRange(start, len)
  requires DiskQueue_HasJournal(disk, start, len)
  requires forall id | id in disk.reqWrites ::
      locDisjointFromCircularJournalRange(
          disk.reqWrites[id].loc, start as uint64, len as uint64)
  ensures Disk_HasJournal(disk.blocks, start, len)
  ensures Disk_Journal(disk.blocks, start, len)
      == DiskQueue_Journal(disk, start, len)
  {
    var dq := DiskQueue_JournalBlockSeq(disk);
    var d := Disk_JournalBlockSeq(disk.blocks);
    var dq_slice := CyclicSlice(dq, start, len);
    var d_slice := CyclicSlice(d, start, len);
    assert |d_slice| == |dq_slice|;
    forall i | 0 <= i < |d_slice|
    ensures d_slice[i] == dq_slice[i]
    {
      var j := JournalPosAdd(start, i);
      calc {
        d_slice[i];
        d[j];
        dq[j];
        dq_slice[i];
      }
    }
    assert d_slice == dq_slice;
  }

  lemma Disk_Journal_empty(disk: DiskState, start: int)
  requires WFRange(start, 0)
  ensures Disk_HasJournal(disk.blocks, start, 0)
  ensures Disk_Journal(disk.blocks, start, 0) == []
  {
    assert CyclicSlice(Disk_JournalBlockSeq(disk.blocks), start, 0)
        == [];
    assert Disk_JournalRange(disk.blocks, start, 0)
        == JournalRangeEmpty();
    parseJournalRangeEmpty();
  }

  lemma DiskQueue_Journal_empty(disk: DiskState, start: int)
  requires WFRange(start, 0)
  requires NoOverlaps(disk.reqWrites)
  ensures DiskQueue_HasJournal(disk, start, 0)
  ensures DiskQueue_Journal(disk, start, 0) == []
  {
    assert CyclicSlice(DiskQueue_JournalBlockSeq(disk), start, 0)
        == [];
    parseJournalRangeEmpty();
    assert DiskQueue_JournalRange(disk, start, 0)
        == JournalRangeEmpty();
  }

  function mapSome<T>(s: seq<T>) : (res : seq<Option<T>>)
  ensures |res| == |s|
  ensures forall i | 0 <= i < |res| :: res[i] == Some(s[i])
  {
    if s == [] then [] else mapSome(DropLast(s)) + [Some(Last(s))]
  }

  lemma concatFold_mapSome_JournalBlocks_eq_self(jr: JournalRange)
  ensures concatFold(mapSome(JournalBlocks(jr))) == jr
  {
    assume false;
  }

  lemma concatFoldAdditive(
      a: seq<Option<JournalRange>>,
      b: seq<Option<JournalRange>>)
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
      JournalRangeConcatAssoc(concatFold(a), concatFold(b[..|b|-1]), b[|b|-1].value);
      calc {
        concatFold(a + b);
        JournalRangeConcat(concatFold((a + b)[..|a+b|-1]), (a+b)[|a+b|-1].value);
        JournalRangeConcat(concatFold(a + b[..|b|-1]), b[|b|-1].value);
        JournalRangeConcat(JournalRangeConcat(concatFold(a), concatFold(b[..|b|-1])), b[|b|-1].value);
        JournalRangeConcat(concatFold(a), JournalRangeConcat(concatFold(b[..|b|-1]), b[|b|-1].value));
        JournalRangeConcat(concatFold(a), concatFold(b));
      }
    }
  }

  lemma Queue_JournalBlockAt_preserved_by_nonoverlapping_write(
      k: DiskConstants, disk: DiskState, disk': DiskState, dop: DiskOp, i: int)
  requires AsyncSectorDisk.RecvWrite(k, disk, disk', dop)
      || AsyncSectorDisk.RecvWrite2(k, disk, disk', dop)
  requires 0 <= i < NumJournalBlocks() as int
  requires AsyncSectorDisk.RecvWrite(k, disk, disk', dop) ==>
      !overlap(dop.reqWrite.loc, JournalRangeLocation(i as uint64, 1))
  requires AsyncSectorDisk.RecvWrite2(k, disk, disk', dop) ==>
      !overlap(dop.reqWrite1.loc, JournalRangeLocation(i as uint64, 1))
  requires AsyncSectorDisk.RecvWrite2(k, disk, disk', dop) ==>
      !overlap(dop.reqWrite2.loc, JournalRangeLocation(i as uint64, 1))
  requires NoOverlaps(disk.reqWrites)
  requires NoOverlaps(disk'.reqWrites)
  ensures Queue_JournalBlockAt(disk.reqWrites, i)
      == Queue_JournalBlockAt(disk'.reqWrites, i)
  {
    var loc := JournalRangeLocation(i as uint64, 1);
    if Queue_JournalBlockAt(disk.reqWrites, i).Some? {
      var id :| id in disk.reqWrites
        && ValidJournalLocation(disk.reqWrites[id].loc)
        && LocationSub(loc, disk.reqWrites[id].loc);
      assert ValidJournalLocation(disk'.reqWrites[id].loc);
      assert LocationSub(loc, disk'.reqWrites[id].loc);
    } else {
      assert Queue_JournalBlockAt(disk'.reqWrites, i).None?;
    }
  }

  lemma DiskQueue_Journal_write_other(
      k: DiskConstants, disk: DiskState, disk': DiskState,
      start: int, len: int, dop: DiskOp)
  requires WFRange(start, len)
  requires AsyncSectorDisk.RecvWrite(k, disk, disk', dop)
  requires ValidLocation(dop.reqWrite.loc);
  requires !ValidJournalLocation(dop.reqWrite.loc);
  requires DiskQueue_HasJournal(disk, start, len)
  requires NoOverlaps(disk'.reqWrites)
  ensures DiskQueue_HasJournal(disk', start, len)
  ensures DiskQueue_Journal(disk', start, len)
      == DiskQueue_Journal(disk, start, len)
  {
    var dq := DiskQueue_JournalBlockSeq(disk);
    var dq' := DiskQueue_JournalBlockSeq(disk');

    var slice := CyclicSlice(dq, start, len);
    var slice' := CyclicSlice(dq', start, len);

    assert |slice'| == |slice|;
    forall i | 0 <= i < |slice'| ensures slice'[i] == slice[i]
    {
      var j := JournalPosAdd(start, i);
      var loc := JournalRangeLocation(j as uint64, 1);
      if overlap(loc, dop.reqWrite.loc) {
        overlappingLocsSameType(loc, dop.reqWrite.loc);
      }
      calc {
        slice'[i];
        dq'[j];
        DiskQueue_JournalBlockAt(disk', j);
        {
          Queue_JournalBlockAt_preserved_by_nonoverlapping_write(
              k, disk, disk', dop, j);
        }
        DiskQueue_JournalBlockAt(disk, j);
        dq[j];
        slice[i];
      }
    }
    assert slice' == slice;
  }

  lemma DiskQueue_Journal_append(
      k: DiskConstants, disk: DiskState, disk': DiskState,
      start: int, len: int, jr: JournalRange,
      dop: DiskOp)
  requires WFRange(start, len)
  requires AsyncSectorDisk.RecvWrite(k, disk, disk', dop)
  requires dop.reqWrite.sector == SectorJournal(jr)
  requires DiskQueue_HasJournal(disk, start, len)
  requires parseJournalRange(jr).Some?
  requires len + JournalRangeLen(jr) <= NumJournalBlocks() as int
  requires JournalPosAdd(start, len) + JournalRangeLen(jr) <= NumJournalBlocks() as int
  requires NoOverlaps(disk'.reqWrites)
  requires dop.reqWrite.loc == JournalRangeLocation(
      JournalPosAdd(start, len) as uint64,
      JournalRangeLen(jr) as uint64)
  ensures DiskQueue_HasJournal(disk', start, len + JournalRangeLen(jr))
  ensures DiskQueue_Journal(disk', start, len + JournalRangeLen(jr))
      == DiskQueue_Journal(disk, start, len) + parseJournalRange(jr).value
  {
    var dq := DiskQueue_JournalBlockSeq(disk);
    var dq' := DiskQueue_JournalBlockSeq(disk');

    var slice := CyclicSlice(dq, start, len);
    var slice_jr := slice + mapSome(JournalBlocks(jr));

    var slice' := CyclicSlice(dq', start, len + JournalRangeLen(jr));

    assert |slice'| == |slice_jr|;
    forall i | 0 <= i < |slice'| ensures slice'[i] == slice_jr[i]
    {
      var j := JournalPosAdd(start, i);
      var loc := JournalRangeLocation(j as uint64, 1);
      if i < len {
        calc {
          slice'[i];
          dq'[j];
          DiskQueue_JournalBlockAt(disk', j);
          {
            Queue_JournalBlockAt_preserved_by_nonoverlapping_write(
                k, disk, disk', dop, j);
          }
          dq[j];
          slice_jr[i];
        }
      } else {
        //assert 0 <= i - len;
        //assert i - len <= JournalRangeLen(jr);

        var loc := JournalRangeLocation(j as uint64, 1);
        assert dop.id in disk'.reqWrites;
        assert ValidJournalLocation(disk'.reqWrites[dop.id].loc);
        assert LocationSub(loc, disk'.reqWrites[dop.id].loc);
        assert disk'.reqWrites[dop.id].sector.SectorJournal?;
        assert 0 <= j - JournalBlockIdx(disk'.reqWrites[dop.id].loc) < 
            JournalRangeLen(disk'.reqWrites[dop.id].sector.journal);

        assert Queue_JournalBlockAt(disk'.reqWrites, j).Some?;
        calc {
          slice'[i];
          dq'[j];
          DiskQueue_JournalBlockAt(disk', j);
          Queue_JournalBlockAt(disk'.reqWrites, j);
          Some(JournalBlockGet(jr, i - len));
          Some(JournalBlocks(jr)[i - len]);
          mapSome(JournalBlocks(jr))[i - len];
          slice_jr[i];
        }
      }
    }
    assert slice' == slice_jr;

    calc {
      concatFold(slice');
      concatFold(slice_jr);
      {
        concatFoldAdditive(slice, mapSome(JournalBlocks(jr)));
      }
      JournalRangeConcat(concatFold(slice),
            concatFold(mapSome(JournalBlocks(jr))));
      {
        concatFold_mapSome_JournalBlocks_eq_self(jr);
      }
      JournalRangeConcat(concatFold(slice), jr);
    }

    parseJournalRangeAdditive(concatFold(slice), jr);
  }

  lemma DiskQueue_Journal_append_wraparound(
      k: DiskConstants, disk: DiskState, disk': DiskState,
      start: int, len: int, jr: JournalRange,
      dop: DiskOp)
  requires WFRange(start, len)
  requires AsyncSectorDisk.RecvWrite2(k, disk, disk', dop)
  requires len + JournalRangeLen(jr) <= NumJournalBlocks() as int
  requires JournalPosAdd(start, len) + JournalRangeLen(jr) >= NumJournalBlocks() as int
  requires dop.reqWrite1.sector == SectorJournal(JournalRangePrefix(jr, NumJournalBlocks() as int - start - len))
  requires dop.reqWrite2.sector == SectorJournal(JournalRangeSuffix(jr, NumJournalBlocks() as int - start - len))
  requires DiskQueue_HasJournal(disk, start, len)
  requires parseJournalRange(jr).Some?
  requires NoOverlaps(disk'.reqWrites)
  requires dop.reqWrite1.loc == JournalRangeLocation(
      JournalPosAdd(start, len) as uint64,
      (NumJournalBlocks() - start as uint64 - len as uint64))
  requires dop.reqWrite2.loc == JournalRangeLocation(
      0,
      JournalRangeLen(jr) as uint64 - (NumJournalBlocks() - start as uint64 - len as uint64))
  ensures DiskQueue_HasJournal(disk', start, len + JournalRangeLen(jr))
  ensures DiskQueue_Journal(disk', start, len + JournalRangeLen(jr))
      == DiskQueue_Journal(disk, start, len) + parseJournalRange(jr).value
  {
    var dq := DiskQueue_JournalBlockSeq(disk);
    var dq' := DiskQueue_JournalBlockSeq(disk');

    var jr1 := JournalRangePrefix(jr, NumJournalBlocks() as int - start - len);
    var jr2 := JournalRangeSuffix(jr, NumJournalBlocks() as int - start - len);
    var len1 := NumJournalBlocks() as int - start - len;

    var slice := CyclicSlice(dq, start, len);
    var slice_jr := slice + mapSome(JournalBlocks(jr));

    var slice' := CyclicSlice(dq', start, len + JournalRangeLen(jr));

    assert |slice'| == |slice_jr|;
    forall i | 0 <= i < |slice'| ensures slice'[i] == slice_jr[i]
    {
      var j := JournalPosAdd(start, i);
      if i < len {
        calc {
          slice'[i];
          dq'[j];
          {
            Queue_JournalBlockAt_preserved_by_nonoverlapping_write(
                k, disk, disk', dop, j);
          }
          dq[j];
          slice_jr[i];
        }
      } else if i < len + len1 {
        assert 0 <= i - len;
        assert i - len <= JournalRangeLen(jr);

        var loc := JournalRangeLocation(j as uint64, 1);
        assert dop.id1 in disk'.reqWrites;
        assert ValidJournalLocation(disk'.reqWrites[dop.id1].loc);
        assert LocationSub(loc, disk'.reqWrites[dop.id1].loc);
        assert disk'.reqWrites[dop.id1].sector.SectorJournal?;
        assert JournalRangeLen(disk'.reqWrites[dop.id1].sector.journal) == len1;
        assert 0
            <= j - JournalBlockIdx(disk'.reqWrites[dop.id1].loc)
            < JournalRangeLen(disk'.reqWrites[dop.id1].sector.journal);

        assert Queue_JournalBlockAt(disk'.reqWrites, j).Some?;
        calc {
          slice'[i];
          dq'[j];
          DiskQueue_JournalBlockAt(disk', j);
          Queue_JournalBlockAt(disk'.reqWrites, j);
          Some(JournalBlockGet(jr1, i - len));
          Some(JournalBlocks(jr1)[i-len]);
          {
            JournalRangePrefixGet(
                jr, NumJournalBlocks() as int - start - len, i - len);
          }
          Some(JournalBlocks(jr)[i-len]);
          mapSome(JournalBlocks(jr))[i - len];
          slice_jr[i];
        }
      } else {
        assert 0 <= i - len;
        assert i - len <= JournalRangeLen(jr);

        var loc := JournalRangeLocation(j as uint64, 1);
        assert dop.id2 in disk'.reqWrites;
        assert ValidJournalLocation(disk'.reqWrites[dop.id2].loc);
        assert LocationSub(loc, disk'.reqWrites[dop.id2].loc);
        assert disk'.reqWrites[dop.id2].sector.SectorJournal?;
        assert 0 <= j - JournalBlockIdx(disk'.reqWrites[dop.id2].loc) < 
            JournalRangeLen(disk'.reqWrites[dop.id2].sector.journal);

        assert Queue_JournalBlockAt(disk'.reqWrites, j).Some?;
        calc {
          slice'[i];
          dq'[j];
          DiskQueue_JournalBlockAt(disk', j);
          Queue_JournalBlockAt(disk'.reqWrites, j);
          Some(JournalBlockGet(jr2, i - len - len1));
          {
            JournalRangeSuffixGet(
                jr, len1, i - len - len1);
          }
          Some(JournalBlockGet(jr, i - len));
          mapSome(JournalBlocks(jr))[i - len];
          slice_jr[i];
        }
      }
    }
    assert slice' == slice_jr;

    calc {
      concatFold(slice');
      concatFold(slice_jr);
      {
        concatFoldAdditive(slice, mapSome(JournalBlocks(jr)));
      }
      JournalRangeConcat(concatFold(slice),
            concatFold(mapSome(JournalBlocks(jr))));
      {
        concatFold_mapSome_JournalBlocks_eq_self(jr);
      }
      JournalRangeConcat(concatFold(slice), jr);
    }

    parseJournalRangeAdditive(concatFold(slice), jr);
  }

  lemma DiskQueue_Journal_ProcessWrite(
      k: DiskConstants, disk: DiskState, disk': DiskState,
      start: int, len: int,
      id: ReqId)
  requires WFRange(start, len)
  requires AsyncSectorDisk.ProcessWrite(k, disk, disk', id)
  requires ValidLocation(disk.reqWrites[id].loc);
  requires DiskQueue_HasJournal(disk, start, len)
  ensures DiskQueue_HasJournal(disk', start, len)
  ensures DiskQueue_Journal(disk', start, len)
       == DiskQueue_Journal(disk, start, len)
  {
    var dq := DiskQueue_JournalBlockSeq(disk);
    var dq' := DiskQueue_JournalBlockSeq(disk');

    var slice := CyclicSlice(dq, start, len);
    var slice' := CyclicSlice(dq', start, len);

    assert |slice'| == |slice|;
    forall i | 0 <= i < |slice'| ensures slice'[i] == slice[i]
    {
      var j := JournalPosAdd(start, i);
      calc {
        slice[i];
        dq[j];
        DiskQueue_JournalBlockAt(disk, j);
        {
          var loc := JournalRangeLocation(j as uint64, 1);
          if overlap(loc, disk.reqWrites[id].loc) {
            journalLength1OverlapImpliesContained(
                j as uint64, disk.reqWrites[id].loc);
          }

          if (Queue_JournalBlockAt(disk.reqWrites, j).Some?) {
            if (Queue_JournalBlockAt(disk'.reqWrites, j).None?) {
              var idx := j - JournalBlockIdx(disk.reqWrites[id].loc);

              assert LogLookupSingleBlockConsistentLoc(disk'.blocks,
                  disk.reqWrites[id].loc, loc, idx as int);

              //assert disk.reqWrites[id].loc in disk'.blocks;
              //assert disk'.blocks[disk.reqWrites[id].loc].SectorJournal?;
              //assert loc.addr as int == disk.reqWrites[id].loc.addr as int + 4096*idx;
              //assert loc.len == 4096;

              assert loc in disk'.blocks;
              assert Disk_JournalBlockAt(disk'.blocks, j).Some?;
              assert Disk_JournalBlockAt(disk'.blocks, j).value
                  == Queue_JournalBlockAt(disk.reqWrites, j).value;
              assert DiskQueue_JournalBlockAt(disk, j)
                  == DiskQueue_JournalBlockAt(disk', j);
            } else {
              assert DiskQueue_JournalBlockAt(disk, j)
                  == DiskQueue_JournalBlockAt(disk', j);
            }
          } else {
            if overlap(loc, disk.reqWrites[id].loc) {
              overlappingLocsSameType(loc, disk.reqWrites[id].loc);
              journalLength1OverlapImpliesContained(
                  j as uint64, disk.reqWrites[id].loc);

              assert id in disk.reqWrites;
              assert ValidJournalLocation(disk.reqWrites[id].loc);
              assert LocationSub(loc, disk.reqWrites[id].loc);

              assert disk.reqWrites[id].sector.SectorJournal?;
              assert 0 <= j - JournalBlockIdx(disk.reqWrites[id].loc) < 
                JournalRangeLen(disk.reqWrites[id].sector.journal);

              assert false;
            }

            if (Queue_JournalBlockAt(disk'.reqWrites, j).None?) {
              assert DiskQueue_JournalBlockAt(disk, j)
                  == Disk_JournalBlockAt(disk.blocks, j)
                  == Disk_JournalBlockAt(disk'.blocks, j)
                  == DiskQueue_JournalBlockAt(disk', j);
            } else {
              assert DiskQueue_JournalBlockAt(disk, j)
                  == DiskQueue_JournalBlockAt(disk', j);
            }
          }
        }
        DiskQueue_JournalBlockAt(disk', j);
        dq'[j];
        slice'[i];
      }
    }
    assert slice' == slice;
  }

  lemma Disk_Journal_ProcessWrite(
      k: DiskConstants, disk: DiskState, disk': DiskState,
      start: int, len: int,
      id: ReqId)
  requires WFRange(start, len)
  requires AsyncSectorDisk.ProcessWrite(k, disk, disk', id)
  requires Disk_HasJournal(disk.blocks, start, len)
  requires locDisjointFromCircularJournalRange(
          disk.reqWrites[id].loc, start as uint64, len as uint64)
  ensures Disk_HasJournal(disk'.blocks, start, len)
  ensures Disk_Journal(disk'.blocks, start, len)
       == Disk_Journal(disk.blocks, start, len)
  {
    var d := Disk_JournalBlockSeq(disk.blocks);
    var d' := Disk_JournalBlockSeq(disk'.blocks);

    var slice := CyclicSlice(d, start, len);
    var slice' := CyclicSlice(d', start, len);

    assert |slice'| == |slice|;
    forall i | 0 <= i < |slice'| ensures slice'[i] == slice[i]
    {
      var j := JournalPosAdd(start, i);
      var loc := JournalRangeLocation(j as uint64, 1);
      assert !overlap(loc, disk.reqWrites[id].loc);
      assert slice[i].Some?;
      assert Disk_JournalBlockAtLoc(disk.blocks, loc).Some?;
      assert loc in disk.blocks;
      assert loc in disk'.blocks;
      assert disk'.blocks[loc] == disk.blocks[loc];
      calc {
        slice[i];
        d[j];
        Disk_JournalBlockAt(disk.blocks, j);
        Disk_JournalBlockAtLoc(disk.blocks, loc);
        Disk_JournalBlockAtLoc(disk'.blocks, loc);
        Disk_JournalBlockAt(disk'.blocks, j);
        {
          assert d'[j] == Disk_JournalBlockAt(disk'.blocks, j);
        }
        d'[j];
        slice'[i];
      }
    }
    assert slice' == slice;
  }

  lemma Disk_JournalRange_Read1(
      disk: DiskState, start: int, len: int)
  requires WFRange(start, len)
  requires 1 <= len
  requires start + len <= NumJournalBlocks() as int
  requires Disk_HasJournalRange(disk.blocks, start, len)
  requires ClosedUnderLogConcatenation(disk.blocks)
  ensures JournalRangeLocation(start as uint64, len as uint64) in disk.blocks
  ensures disk.blocks[JournalRangeLocation(start as uint64, len as uint64)].SectorJournal?
  ensures Disk_JournalRange(disk.blocks, start, len)
      == disk.blocks[JournalRangeLocation(start as uint64, len as uint64)].journal
  {
    if len == 1 {
      var slice := CyclicSlice(Disk_JournalBlockSeq(disk.blocks), start, len);
      assert slice[0].Some?;
      assert Disk_JournalBlockSeq(disk.blocks)[start]
          == Disk_JournalBlockAt(disk.blocks, start);
      assert slice[0] == Disk_JournalBlockAt(disk.blocks, start);
      JournalRangeConcatEmpty'(slice[0].value);
      assert concatFold(slice)
          == JournalRangeConcat(JournalRangeEmpty(), slice[0].value)
          == slice[0].value;
    } else {
      var slice := CyclicSlice(Disk_JournalBlockSeq(disk.blocks), start, len);
      var slice1 := CyclicSlice(Disk_JournalBlockSeq(disk.blocks), start, len-1);
      assert slice1 == DropLast(slice);
      Disk_JournalRange_Read1(disk, start, len-1);

      var loc1 := JournalRangeLocation(start as uint64, len as uint64 - 1);
      var loc2 := JournalRangeLocation(start as uint64 + len as uint64 - 1, 1);
      var loc3 := JournalRangeLocation(start as uint64, len as uint64);
      assert ClosedUnderLogConcatenationLocs(
          disk.blocks, loc1, loc2, loc3);

      assert slice[len - 1].Some?;

      assert loc1 in disk.blocks;
      assert loc2 in disk.blocks;
      assert disk.blocks[loc1].SectorJournal?;
      assert disk.blocks[loc2].SectorJournal?;
      assert loc2.addr as int == loc1.addr as int + loc1.len as int;
      assert loc3.addr == loc1.addr;
      assert loc3.len as int == loc1.len as int + loc2.len as int;
      assert loc3 in disk.blocks;
    }
  }

  lemma Disk_JournalRange_Read2(
      disk: DiskState, start: int, len: int)
  requires WFRange(start, len)
  requires 1 <= len
  requires start + len > NumJournalBlocks() as int
  requires Disk_HasJournalRange(disk.blocks, start, len)
  requires ClosedUnderLogConcatenation(disk.blocks)
  ensures JournalRangeLocation(start as uint64, NumJournalBlocks() - start as uint64) in disk.blocks
  ensures disk.blocks[JournalRangeLocation(start as uint64, NumJournalBlocks() - start as uint64)].SectorJournal?
  ensures JournalRangeLocation(0, len as uint64 - (NumJournalBlocks() - start as uint64)) in disk.blocks
  ensures disk.blocks[JournalRangeLocation(0, len as uint64 - (NumJournalBlocks() - start as uint64))].SectorJournal?
  ensures Disk_JournalRange(disk.blocks, start, len)
      == JournalRangeConcat(
        disk.blocks[JournalRangeLocation(start as uint64, NumJournalBlocks() - start as uint64)].journal,
        disk.blocks[JournalRangeLocation(0, len as uint64 - (NumJournalBlocks() - start as uint64))].journal)
  {
    var slice := CyclicSlice(Disk_JournalBlockSeq(disk.blocks), start, len);
    var slice1 := CyclicSlice(Disk_JournalBlockSeq(disk.blocks), start, NumJournalBlocks() as int - start);
    var slice2 := CyclicSlice(Disk_JournalBlockSeq(disk.blocks), 0, len - (NumJournalBlocks() as int - start));
    assert slice == slice1 + slice2;
    assert slice1 == slice[.. NumJournalBlocks() as int - start];
    assert slice2 == slice[NumJournalBlocks() as int - start ..];

    Disk_JournalRange_Read1(disk, start, NumJournalBlocks() as int - start);
    Disk_JournalRange_Read1(disk, 0, len - (NumJournalBlocks() as int - start));

    concatFoldAdditive(slice1, slice2);
  }

  lemma Disk_Journal_Read1(
      disk: DiskState, start: int, len: int)
  requires WFRange(start, len)
  requires 1 <= len
  requires start + len <= NumJournalBlocks() as int
  requires Disk_HasJournal(disk.blocks, start, len)
  ensures JournalRangeLocation(start as uint64, len as uint64) in disk.blocks
  ensures disk.blocks[JournalRangeLocation(start as uint64, len as uint64)].SectorJournal?
  ensures Some(Disk_Journal(disk.blocks, start, len))
      == parseJournalRange(disk.blocks[JournalRangeLocation(start as uint64, len as uint64)].journal)
  {
    Disk_JournalRange_Read1(disk, start, len);
  }

  lemma Disk_Journal_Read2(
      disk: DiskState, start: int, len: int)
  requires WFRange(start, len)
  requires 1 <= len
  requires start + len > NumJournalBlocks() as int
  requires Disk_HasJournal(disk.blocks, start, len)
  requires ClosedUnderLogConcatenation(disk.blocks)
  ensures JournalRangeLocation(start as uint64, NumJournalBlocks() - start as uint64) in disk.blocks
  ensures disk.blocks[JournalRangeLocation(start as uint64, NumJournalBlocks() - start as uint64)].SectorJournal?
  ensures JournalRangeLocation(0, len as uint64 - (NumJournalBlocks() - start as uint64)) in disk.blocks
  ensures disk.blocks[JournalRangeLocation(0, len as uint64 - (NumJournalBlocks() - start as uint64))].SectorJournal?
  ensures Some(Disk_Journal(disk.blocks, start, len))
      == parseJournalRange(JournalRangeConcat(
        disk.blocks[JournalRangeLocation(start as uint64, NumJournalBlocks() - start as uint64)].journal,
        disk.blocks[JournalRangeLocation(0, len as uint64 - (NumJournalBlocks() - start as uint64))].journal))
  {
    Disk_JournalRange_Read2(disk, start, len);
  }
}
