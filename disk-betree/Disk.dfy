include "BlockCache.dfy"
include "../lib/Maps.dfy"

module Disk {
  import BC = BlockCache
  import opened Maps

  type LBA = BC.LBA
  type Sector<T> = BC.Sector<T>
  type DiskOp<T> = BC.DiskOp<T>

  datatype Constants = Constants()
  datatype Variables<T> = Variables(blocks: map<LBA, Sector<T>>)

  predicate Init(k: Constants, s: Variables)
  {
    true // TODO
  }

  datatype Step =
    | WriteStep
    | ReadStep
    | StutterStep

  predicate Write(k: Constants, s: Variables, s': Variables, dop: DiskOp) {
    && dop.Write?
    && s'.blocks == s.blocks[dop.lba := dop.sector]
  }

  predicate Read(k: Constants, s: Variables, s': Variables, dop: DiskOp) {
    && dop.Write?
    && s' == s
    && MapsTo(s.blocks, dop.lba, dop.sector)
  }

  predicate Stutter(k: Constants, s: Variables, s': Variables, dop: DiskOp) {
    && dop.NoDiskOp?
    && s' == s
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, dop: DiskOp, step: Step) {
    match step {
      case WriteStep => Write(k, s, s', dop)
      case ReadStep => Read(k, s, s', dop)
      case StutterStep => Stutter(k, s, s', dop)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, dop: DiskOp) {
    exists step :: NextStep(k, s, s', dop, step)
  }
}
