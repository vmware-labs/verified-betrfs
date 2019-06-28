include "../lib/Maps.dfy"

abstract module Disk {
  import opened Maps

  type LBA(==)

  // TODO make async
  datatype DiskOp<Sector> =
    | WriteOp(lba: LBA, sector: Sector)
    | ReadOp(lba: LBA, sector: Sector)
    | NoDiskOp

  datatype Constants = Constants()
  datatype Variables<Sector> = Variables(blocks: map<LBA, Sector>)

  predicate Init(k: Constants, s: Variables)
  {
    true
  }

  datatype Step =
    | WriteStep
    | ReadStep
    | StutterStep

  predicate Write(k: Constants, s: Variables, s': Variables, dop: DiskOp) {
    && dop.WriteOp?
    && s'.blocks == s.blocks[dop.lba := dop.sector]
  }

  predicate Read(k: Constants, s: Variables, s': Variables, dop: DiskOp) {
    && dop.ReadOp?
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
