include "DiskLogSystem.dfy"

module DiskLogSystemInv {
  import opened DiskLogSystem

  type Index = M.LBAType.LogSpec.Index

  function IndexCtor(idx: int) : M.LBAType.LogSpec.Index {
    M.LBAType.LogSpec.Index(idx)
  }

  predicate DiskHasValidSuperblock(k: D.Constants, s: M.DiskVariables)
  {
    && M.SuperblockLBA() in s.blocks
    && var superblock := s.blocks[M.SuperblockLBA()];
    && superblock.SuperblockSector?
  }

  function LengthFromSuperblock(k: D.Constants, s: M.DiskVariables) : int
    requires DiskHasValidSuperblock(k, s)
  {
    s.blocks[M.SuperblockLBA()].superblock.length
  }

  predicate IndexValidForDiskLog(k: D.Constants, s: M.DiskVariables, idx: Index)
    requires DiskHasValidSuperblock(k, s)
  {
    0 <= idx.idx < LengthFromSuperblock(k, s)
  }

  predicate DiskIsValidLog(k: D.Constants, s: M.DiskVariables)
  {
    && DiskHasValidSuperblock(k, s)
    && 0 <= LengthFromSuperblock(k, s)
    && (forall idx :: IndexValidForDiskLog(k, s, idx) ==> (
      && var lba := M.LBAType.indexToLBA(idx);
      && lba in s.blocks
      && s.blocks[lba].LogSector?
    ))
  }

  function ElementFromDiskLog(k: D.Constants, s: M.DiskVariables, idx: Index) : M.L.Element
    requires DiskIsValidLog(k, s)
    requires 0 <= idx.idx < LengthFromSuperblock(k, s)
  {
    s.blocks[M.LBAType.indexToLBA(idx)].element
  }

  predicate MemoryMatchesDisk(k: Constants, s: Variables)
    requires DiskIsValidLog(k.disk, s.disk)
  {
    forall idx: Index :: 0 <= idx.idx < |s.machine.log| ==> (
      && IndexValidForDiskLog(k.disk, s.disk, idx)
      && s.machine.log[idx.idx] == ElementFromDiskLog(k.disk, s.disk, idx)
    )
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && DiskIsValidLog(k.disk, s.disk)
    && MemoryMatchesDisk(k, s)
  }
}
