include "DiskBetree.dfy"

module BlockCache {
  datatype Constants = Constants()

  // psssst T = Node but dodn't tell anybody
  import DiskBetree
  type T<Value> = DiskBetree.Node<Value>
  function Successor(node: T): iset<Reference> { node.children.Values }

  // Stuff for communicating with Disk (probably move to another file?)

  datatype Superblock = Superblock(
      lbas: map<Reference, LBA>,
      refcounts: map<Reference, int>)

  datatype Sector =
    | SectorBlock(block: T)
    | SectorSuperblock(superblock)

  // TODO make async
  datatype DiskOp =
    | Write(lba: LBA, sector: Sector)
    | Read(lba: LBA, sector: Sector)
    | NoDiskOp

  // BlockCache stuff

  datatype CacheLine<T> = CacheLine(block: T)

  datatype Variables =
    | Ready(
        persistentSuperblock: SuperBlock,
        ephemeralSuperblock: SuperBlock,
        cache: map<Reference, CacheLine>)
    | Unready

  datatype Step =
    | WriteBackStep(ref: Reference)
    | WriteBackSuperblockStep
    | DirtyStep(ref: Reference, block: T)
    | Alloc(ref: Reference, block: T)
    | Unalloc(ref: Reference)
    | PageInStep(ref: Reference)
    | PageInSuperblockStep
    | EvictStep(ref: Reference)
    // TODO page in superblock

  predicate refCountsChangeConsistently(s: Variables, s': Variables, ref: Reference)
  {
    forall 
  }

  predicate WriteBack(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.Write?
    && ref in s.cache
    && dop.lba !in persistentSuperblock.lbas.Values
    && dop.lba !in ephemeralSuperblock.lbas.Values
    && dop.sector == SectorBlock(s.cache[dop.lba].block)
    && s'.Ready?
    && s'.persistentSuperblock == s.persistentSuperblock
    && s'.ephemeralSuperblock.lbas == s.ephemeralSuperblock.lbas[ref := dop.lba]
    && s'.ephemeralSuperblock.refcounts == s.ephemeralSuperblock.refcounts
    && s'.cache == s.cache
  }

  predicate WriteBackSuperblock(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && s.Ready?
    && dop.Write?
    && dop.lba == SuperblockLBA(k)
    && dop.sector == SectorSuperblock(s.ephemeralSuperblock)
    && s.cache.Keys <= s.ephemeralSuperblock.lbas.Keys
    && s' == s[persistentSuperblock := s.ephemeralSuperblock]
  }

  predicate Dirty(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference, block: T)
  {
    // Possibly allocs ref, possibly overwrites it.
    && s.Ready?
    && dop.NoDiskOp
    && ref in s.cache
    && s'.Ready?
    && s'.cache == s.cache[ref := CacheLine(block)]
    && s'.persistentSuperblock == s.persistenSuperblock

    && s'.ephemeralSuperblock.lbas == s.ephemeralSuperblock.lbas[ref := null]

    && refCountsChangeConsistently(s.ephemeralSuperblock.refcounts, s'.ephemeralSuperblock.refcounts, s.cache, ref)
  }

  predicate Alloc(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference, block: T)
  {
    // Possibly allocs ref, possibly overwrites it.
    && s.Ready?
    && dop.NoDiskOp
    && ref !in s.cache
    && ref !in s.ephemeralSuperblock.refcounts
    && s'.Ready?
    && s'.cache == s.cache[ref := CacheLine(block)]
    && s'.persistentSuperblock == s.persistenSuperblock

    && s'.ephemeralSuperblock.lbas == s.ephemeralSuperblock.lbas

    && refCountsChangeConsistently(s.ephemeralSuperblock.refcounts, s'.ephemeralSuperblock.refcounts, s.cache, ref)
    && s'.ephemeralSuperblock.refcounts[ref] == 0
  }

  predicate Unalloc(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.NoDiskOp
    && ref in s.ephemeralSuperblock.refcounts
    && s'.Ready?
    && s'.persistentSuperblock == s.persistentSuperblock
    && s'.ephemeralSuperblock.lbas == RemoveFromMap(s.ephemeralSuperblock.lbas, ref)
    && s'.cache == RemoveFromMap(s.cache, ref)
    && refCountsChangeConsistently(s.ephemeralSuperblock.refcounts, s'.ephemeralSuperblock.refcounts, s.cache, ref)
    && ref !in s'.ephemeralSuperblock.refcounts
  }

  predicate PageIn(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.Read
    && ref in s.ephemeralSuperblock.refcounts
    && ref in s.ephemeralSuperblock.lbas
    && s.ephemeralSuperblock[ref].lba == dop.lba
    && dop.sector.SectorBlock?
    && s' == s[cache := s.cache[ref := CacheLine(dop.sector.block)]]
  }

  predicate PageInSuperblock(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Unready?
    && dop.Read
    && dop.lba == SuperblockLBA
    && dop.sector.superblock?
    && s' == Ready(dop.sector.superblock, dop.sector.superblock, map[])
  }

  predicate Evict(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.NoDiskOp
    && ref in s.cache
    && ref in s.ephemeralSuperblock.lbas
    && s' == s[cache := RemoveFromMap(s.cache, ref)]
  }

  predicate WFSuperblock(superblock: Superblock)
  {
    && SuperBlockLBA !in superblock.lbas.Values
    && superblock.lbas.Keys <= superblock.refcounts.Keys
  }

  predicate Init(k: Constants, s: Variables)
  {
    s == Unready(map[])
  }

  predicate Inv(k: Constants, s: Variables)
  {
    match s {
      case Ready(persistentSuperblock, ephemeralSuperblock, cache) => {
        && WFSuperblock(s.persistentSuperblock)
        && WFSuperblock(s.ephemeralSuperblock)
        && s.persistentSuperblock.lbas.Keys == s.persistentSuperblock.refcounts.Keys
        && s.cache.Keys <= s.ephemeralSuperblock.refcounts
      }
      case Unready(cache) => {
        true
      }
    }
  }
}
