include "DiskBetree.dfy"

module BlockCache {
  datatype Constants = Constants()

  // psssst T = Node but dodn't tell anybody
  import DiskBetree
  type T<Value> = DiskBetree.Node<Value>
  function Successor(node: T): iset<Reference> { node.children.Values }

  // Stuff for communicating with Disk (probably move to another file?)

  type Superblock = map<Reference, (LBA, refcount)>

  datatype Sector =
    | SectorBlock(block: T)
    | SectorSuperblock(superblock)

  // TODO make async
  datatype DiskOp =
    | Write(lba: LBA, sector: Sector)
    | Read(lba: LBA, sector: Sector)
    | NoDiskOp

  // BlockCache stuff

  datatype Status = Dirty | Clean
  datatype CacheLine<T> = CacheLine(block: T, status: Status)

  datatype Variables =
    | Ready(
        persistentSuperblock: SuperBlock?,
        ephemeralSuperblock: SuperBlock?,
        cache: map<Reference, CacheLine>)
    | Unready(
        cache: map<Reference, CacheLine>)

  datatype Step =
    | WriteBackStep(ref: Reference)
    | WriteBackSuperblockStep
    | DirtyStep(ref: Reference, block: T)
    | Unalloc(ref: Reference)
    | PageInStep(ref: Reference)
    | PageInSuperblockStep
    | EvictStep(ref: Reference)
    // TODO page in superblock

  predicate WriteBack(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.Write?
    && ref in s.cache
    && dop.lba !in persistentSuperblock.Values
    && dop.lba !in ephemeralSuperblock.Values
    && dop.sector == SectorBlock(s.cache[dop.lba].block)
    && s'.Ready?
    && s'.persistentSuperblock == s.persistentSuperblock
    && s'.ephemeralSuperblock == s.ephemeralSuperblock[ref := dop.lba]
    && s'.cache == s.cache[ref := s.cache[ref][status := Clean]]
  }

  predicate WriteBackSuperblock(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && s.Ready?
    && dop.Write?
    && dop.lba == SuperblockLBA(k)
    && dop.sector == SectorSuperblock(s.ephemeralSuperblock)
    && (forall cacheLine :: cacheLine in s.cache.Values ==> cacheLine.status == Clean)
    && s' == s[persistentSuperblock := s.ephemeralSuperblock]
  }

  predicate Dirty(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference, block: T)
  {
    // Possibly allocs ref, possibly overwrites it.
    && dop.NoDiskOp
    && s' == s[cache := s.cache[ref := CacheLine(block, Dirty)]]
  }

  predicate Unalloc(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.NoDiskOp
    && ref in s.ephemeralSuperblock
    && s'.Ready?
    && s'.persistentSuperblock == s.persistentSuperblock
    && s'.ephemeralSuperblock == RemoveFromMap(s.ephemeralSuperblock, ref)
    && s'.cache == RemoveFromMap(s.cache, ref)
  }

  predicate PageIn(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.Read
    && ref in s.cache ==> s.cache[ref].status == Clean
    && ref in s.ephemeralSuperblock
    && s.ephemeralSuperblock[ref] == dop.lba
    && dop.sector.SectorBlock?
    && s' == s[cache := s.cache[ref := CacheLine(dop.sector.block, Clean)]]
  }

  predicate PageInSuperblock(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Unready?
    && dop.Read
    && dop.lba == SuperblockLBA
    && dop.sector.superblock?
    && s' == Ready(dop.sector.superblock, dop.sector.superblock, s.cache)
  }

  predicate Evict(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.NoDiskOp
    && ref in s.cache
    && s.cache[ref].status == Clean
    && s' == s[cache := RemoveFromMap(s.cache, ref)]
  }

  predicate WFSuperblock(superblock: Superblock)
  {
    SuperBlockLBA !in superblock.Values
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
        && (forall ref :: ref in s.cache.keys && s.cache.keys[ref].status == Clean ==> ref in s.ephemeralSuperblock)
      }
      case Unready(cache) => {
        && (forall ref :: ref in s.cache.keys && s.cache.keys[ref].status == Dirty)
      }
    }
  }
}
