include "CommitterModel.i.dfy"
include "StateModel.i.dfy"
include "IOModel.i.dfy"

module CommitterInitModel {
  import opened NativeTypes
  import opened Options

  import opened DiskLayout
  import opened InterpretationDiskOps
  import opened ViewOp
  import JournalCache

  import opened CommitterModel
  import opened StateModel
  import opened IOModel

  function {:opaque} PageInSuperblockReq(k: Constants, cm: CM, io: IO, which: uint64) : (res : (CM, IO))
  requires which == 0 || which == 1
  requires which == 0 ==> cm.superblock1.SuperblockUnfinished?
  requires which == 1 ==> cm.superblock2.SuperblockUnfinished?
  requires io.IOInit?
  requires cm.status.StatusLoadingSuperblock?
  {
    if which == 0 then (
      if cm.superblock1Read.None? then (
        var loc := Superblock1Location();
        var (id, io') := RequestRead(io, loc);
        var cm' := cm.(superblock1Read := Some(id));
        (cm', io')
      ) else (
        (cm, io)
      )
    ) else (
      if cm.superblock2Read.None? then (
        var loc := Superblock2Location();
        var (id, io') := RequestRead(io, loc);
        var cm' := cm.(superblock2Read := Some(id));
        (cm', io')
      ) else (
        (cm, io)
      )
    )
  }

  lemma PageInSuperblockReqCorrect(k: Constants,
      cm: CM, io: IO, which: uint64)
  requires CommitterModel.WF(cm)
  requires PageInSuperblockReq.requires(k, cm, io, which)
  ensures var (cm', io') := PageInSuperblockReq(k, cm, io, which);
    && CommitterModel.WF(cm')
    && ValidDiskOp(diskOp(io'))
    && JournalCache.Next(Ik(k).jc,
        CommitterModel.I(cm),
        CommitterModel.I(cm'),
        IDiskOp(diskOp(io')).jdop,
        JournalInternalOp)
  {
    reveal_PageInSuperblockReq();
    var (cm', io') := PageInSuperblockReq(k, cm, io, which);

    var loc;
    if which == 0 {
      loc := Superblock1Location();
    } else {
      loc := Superblock2Location();
    }
    RequestReadCorrect(io, loc);

    if (which == 0 && cm.superblock1Read.None?)
      || (which == 1 && cm.superblock2Read.None?)
    {
      assert JournalCache.PageInSuperblockReq(Ik(k).jc,
          CommitterModel.I(cm),
          CommitterModel.I(cm'),
          IDiskOp(diskOp(io')).jdop,
          JournalInternalOp, which as int);
      assert JournalCache.NextStep(Ik(k).jc,
          CommitterModel.I(cm),
          CommitterModel.I(cm'),
          IDiskOp(diskOp(io')).jdop,
          JournalInternalOp,
          JournalCache.PageInSuperblockReqStep(which as int));
    } else {
      assert JournalCache.NoOp(Ik(k).jc,
          CommitterModel.I(cm),
          CommitterModel.I(cm'),
          IDiskOp(diskOp(io')).jdop,
          JournalInternalOp);
      assert JournalCache.NextStep(Ik(k).jc,
          CommitterModel.I(cm),
          CommitterModel.I(cm'),
          IDiskOp(diskOp(io')).jdop,
          JournalInternalOp,
          JournalCache.NoOpStep);

    }
  }
}
