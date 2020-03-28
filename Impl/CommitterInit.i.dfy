include "CommitterModel.i.dfy"
include "StateModel.i.dfy"

module CommitterInit {
  import opened CommitterModel
  import opened StateModel
  import opened IOModel

  function PageInSuperblockReq(cm: CommitterModel, io: IO, which: uint64)
  requires which == 0 || which == 1
  requires io.IOInit?
  requires cm.StatusLoadingSuperblock?
  {
    if which == 0 then (
      if cm.superblock1Read.None? then (
        var loc := Superblock1Location()
        var (id, io') := RequestRead(io, loc);
        var s' := cm.(superblock1Read := Some(id))
        (s', io')
      ) else (
        (s, io)
      )
    ) else (
      if cm.superblock2Read.None? then (
        var loc := Superblock2Location()
        var (id, io') := RequestRead(io, loc);
        var s' := cm.(superblock2Read := Some(id))
        (s', io')
      ) else (
        (s, io)
      )
    )
  }
}
