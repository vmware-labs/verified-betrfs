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

  predicate IsALogSectorBlock(blocks: map<M.LBAType.LBA, M.Sector>, idx: Index)
  {
    && var lba := M.LBAType.indexToLBA(idx);
    && lba in blocks
    && blocks[lba].LogSector?
  }

  predicate DiskIsValidLog(k: D.Constants, s: M.DiskVariables)
  {
    && DiskHasValidSuperblock(k, s)
    && 0 <= LengthFromSuperblock(k, s)
    && (forall idx :: IndexValidForDiskLog(k, s, idx) ==> IsALogSectorBlock(s.blocks, idx))
  }

  function ElementFromDiskLog(k: D.Constants, s: M.DiskVariables, idx: Index) : M.L.Element
    requires DiskIsValidLog(k, s)
    requires IsALogSectorBlock(s.blocks, idx)
  {
    s.blocks[M.LBAType.indexToLBA(idx)].element
  }

  predicate StagedTrailsLogLength(k: Constants, s: Variables)
  {
    s.machine.stagedLength <= |s.machine.log|
  }

  predicate MemoryMatchesDisk(k: Constants, s: Variables)
    requires DiskIsValidLog(k.disk, s.disk)
  {
    forall idx: Index :: 0 <= idx.idx < |s.machine.log| && (
      || idx.idx < s.machine.stagedLength
      || IndexValidForDiskLog(k.disk, s.disk, idx)) ==> (
        && IsALogSectorBlock(s.disk.blocks, idx)
        && s.machine.log[idx.idx] == ElementFromDiskLog(k.disk, s.disk, idx)
    )
  }

  predicate MachinePersistentWhenReadyMatchesDiskSuperblock(k: Constants, s: Variables)
    requires DiskHasValidSuperblock(k.disk, s.disk)
  {
    s.machine.cachedSuperblock.Ready? ==> s.machine.cachedSuperblock.superblock.length == LengthFromSuperblock(k.disk, s.disk) 
  }

  predicate LogIsZeroLengthWhenUnready(k: Constants, s: Variables)
  {
    s.machine.cachedSuperblock.Unready? ==> |s.machine.log| == 0
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && DiskIsValidLog(k.disk, s.disk)
    && MachinePersistentWhenReadyMatchesDiskSuperblock(k, s)
    && StagedTrailsLogLength(k, s)
    && MemoryMatchesDisk(k, s)
    && LogIsZeroLengthWhenUnready(k, s)
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables)
    requires Inv(k, s)
    requires Next(k, s, s')
    ensures Inv(k, s')
  {
  }
}

