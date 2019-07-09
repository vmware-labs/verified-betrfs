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

  // export S provides Index, LBA, SuperblockLBA, indexToLBA
  // export extends S
	// export Internal reveals *
}

module DiskLog {
  import L = LogSpec

  import D = Disk

  import LBAType

  type Index = LBAType.Index

  type Element = L.Element

  datatype Constants = Constants()
  type Log = seq<Element>
  datatype Superblock = Superblock(length: int)
  datatype CachedSuperblock = Unready | Ready(superblock: Superblock)
  // TODO: rename 'persistent'
  datatype Variables = Variables(log: Log, persistent: CachedSuperblock, stagedLength: int)

  function method SuperblockLBA() : LBAType.LBA { LBAType.SuperblockLBA() }

  datatype Sector = SuperblockSector(superblock: Superblock) | LogSector(element: Element)

  type DiskOp = D.DiskOp<LBAType.LBA, Sector>
  type DiskVariables = D.Variables<LBAType.LBA, Sector>

  predicate Mkfs(k: Constants, disk_k: D.Constants, disk_s: DiskVariables)
  {
    && disk_s == D.Variables(map[SuperblockLBA() := SuperblockSector(Superblock(0))])
  }

  predicate Init(k: Constants, s: Variables)
  {
    s == Variables([], Unready, 0)
  }

  predicate SupersedesDisk(k: Constants, s: Variables)
  {
    && s.persistent.Ready?
    && s.persistent.superblock.length <= |s.log|
  }

  predicate Query(k: Constants, s: Variables, s': Variables, diskOp: DiskOp, idx: Index, result: Element)
  {
    && 0 <= idx.idx < |s.log|
    && result == s.log[idx.idx]
    && diskOp == D.NoDiskOp
    && s' == s
  }

  predicate FetchSuperblock(k: Constants, s: Variables, s': Variables, diskOp: DiskOp, length: int)
  {
    && s.persistent == Unready
    && diskOp == D.ReadOp(SuperblockLBA(), SuperblockSector(Superblock(length)))
    && s'.log == s.log
    && s'.persistent == Ready(Superblock(length))
    && s'.stagedLength == s.stagedLength
  }

  predicate FetchElement(k: Constants, s: Variables, s': Variables, diskOp: DiskOp, idx: Index, element: Element)
  {
    && s.persistent.Ready?
    && idx.idx < s.persistent.superblock.length
    && |s.log| == idx.idx
    && diskOp == D.ReadOp(LBAType.indexToLBA(idx), LogSector(element))
    && s'.log == s.log + [element]
    && s'.persistent == s.persistent
    && s'.stagedLength == |s'.log|
  }

  predicate Append(k: Constants, s: Variables, s': Variables, diskOp: DiskOp, element: Element)
  {
    && SupersedesDisk(k, s)
    && diskOp == D.NoDiskOp
    && s'.log == s.log + [element]
    && s'.persistent == s.persistent
    && s'.stagedLength == s.stagedLength
  }

  predicate StageElement(k: Constants, s: Variables, s': Variables, diskOp: DiskOp)
  {
    var stagingIndex := L.Index(s.stagedLength);

    && SupersedesDisk(k, s)
    && 0 <= stagingIndex.idx < |s.log| // maintained by invariant (not a runtime check)
    && diskOp == D.WriteOp(LBAType.indexToLBA(stagingIndex), LogSector(s.log[stagingIndex.idx]))
    && s'.log == s.log
    && s'.persistent == s.persistent
    && s'.stagedLength == s.stagedLength + 1
  }

  predicate Flush(k: Constants, s: Variables, s': Variables, diskOp: DiskOp)
  {
    var newSuperblock := Superblock(s.stagedLength);

    && SupersedesDisk(k, s)
    && s.stagedLength == |s.log| // partial syncs are not allowed by the CrashSafeLog model
    && diskOp == D.WriteOp(SuperblockLBA(), SuperblockSector(newSuperblock))
    && s'.log == s.log
    && s'.persistent == Ready(newSuperblock)
    && s'.stagedLength == s.stagedLength
  }

  predicate Stutter(k: Constants, s: Variables, s': Variables, diskOp: DiskOp)
  {
    && diskOp == D.NoDiskOp
    && s' == s
  }

  datatype Step =
      | QueryStep(idx: Index, result: Element)
      | FetchSuperblockStep(length: int)
      | FetchElementStep(idx: Index, element: Element)
      | AppendStep(element: Element)
      | StageElementStep()
      | FlushStep()
      | StutterStep()

  predicate NextStep(k:Constants, s:Variables, s':Variables, diskOp: DiskOp, step: Step)
  {
      match step {
        case QueryStep(idx: Index, result: Element) => Query(k, s, s', diskOp, idx, result)
        case FetchSuperblockStep(length: int) => FetchSuperblock(k, s, s', diskOp, length)
        case FetchElementStep(idx: Index, element: Element) => FetchElement(k, s, s', diskOp, idx, element)
        case AppendStep(element: Element) => Append(k, s, s', diskOp, element)
        case StageElementStep() => StageElement(k, s, s', diskOp)
        case FlushStep() => Flush(k, s, s', diskOp)
        case StutterStep() => Stutter(k, s, s', diskOp)
      }
  }

  predicate Next(k:Constants, s:Variables, s':Variables, diskOp: DiskOp)
  {
      exists step :: NextStep(k, s, s', diskOp, step)
  }
}
