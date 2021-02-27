// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "Disk.dfy"
include "LogSpec.dfy"

module LBAType {
  import LogSpec

  type Index = LogSpec.Index

  type LBA(==,!new) = int
  function method SuperblockLBA() : LBA { 0 }

  function method indexToLBA(idx: Index) : LBA
  {
    idx.idx + 1
  }
}

module DiskLog {
  import L = LogSpec

  import D = Disk

  import LBAType

  type Index = LBAType.Index

  type Element = L.Element

  type Log = seq<Element>
  datatype Superblock = Superblock(length: int)
  datatype CachedSuperblock = Unready | Ready(superblock: Superblock)

  state machine k() s(log: Log, cachedSuperblock: CachedSuperblock, stagedLength: int) step(diskOp: DiskOp)

  function method SuperblockLBA() : LBAType.LBA { LBAType.SuperblockLBA() }

  datatype Sector = SuperblockSector(superblock: Superblock) | LogSector(element: Element)

  type DiskOp = D.DiskOp<LBAType.LBA, Sector>
  type DiskVariables = D.Variables<LBAType.LBA, Sector>

  predicate Mkfs(k: Constants, disk_k: D.Constants, disk_s: DiskVariables)
  {
    && disk_s == D.Variables(map[SuperblockLBA() := SuperblockSector(Superblock(0))])
  }

  init
  {
    s == Variables([], Unready, 0)
  }

  predicate SupersedesDisk(k: Constants, s: Variables)
  {
    && s.cachedSuperblock.Ready?
    && s.cachedSuperblock.superblock.length <= |s.log|
  }

  step Query(idx: Index, result: Element)
  {
    && 0 <= idx.idx < |s.log|
    && result == s.log[idx.idx]
    && diskOp == D.NoDiskOp
    && s' == s
  }

  step FetchSuperblock(length: int)
  {
    && s.cachedSuperblock == Unready
    && diskOp == D.ReadOp(SuperblockLBA(), SuperblockSector(Superblock(length)))
    && s'.log == s.log
    && s'.cachedSuperblock == Ready(Superblock(length))
    && s'.stagedLength == s.stagedLength
  }

  step FetchElement(idx: Index, element: Element)
  {
    && s.cachedSuperblock.Ready?
    && idx.idx < s.cachedSuperblock.superblock.length
    && |s.log| == idx.idx
    && diskOp == D.ReadOp(LBAType.indexToLBA(idx), LogSector(element))
    && s'.log == s.log + [element]
    && s'.cachedSuperblock == s.cachedSuperblock
    && s'.stagedLength == |s'.log|
  }

  step Append(element: Element)
  {
    && SupersedesDisk(k, s)
    && diskOp == D.NoDiskOp
    && s'.log == s.log + [element]
    && s'.cachedSuperblock == s.cachedSuperblock
    && s'.stagedLength == s.stagedLength
  }

  step StageElement()
  {
    var stagingIndex := L.Index(s.stagedLength);

    && SupersedesDisk(k, s)
    && 0 <= stagingIndex.idx < |s.log| // maintained by invariant (not a runtime check)
    && diskOp == D.WriteOp(LBAType.indexToLBA(stagingIndex), LogSector(s.log[stagingIndex.idx]))
    && s'.log == s.log
    && s'.cachedSuperblock == s.cachedSuperblock
    && s'.stagedLength == s.stagedLength + 1
  }

  step Flush()
  {
    var newSuperblock := Superblock(s.stagedLength);

    && SupersedesDisk(k, s)
    && s.stagedLength == |s.log| // partial syncs are not allowed by the CrashSafeLog model
    && diskOp == D.WriteOp(SuperblockLBA(), SuperblockSector(newSuperblock))
    && s'.log == s.log
    && s'.cachedSuperblock == Ready(newSuperblock)
    && s'.stagedLength == s.stagedLength
  }

  step Stutter()
  {
    && diskOp == D.NoDiskOp
    && s' == s
  }
}
