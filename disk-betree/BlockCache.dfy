

module BlockCache {
  datatype Constants = Constants()

  // psssst T = Node but dodn't tell anybody
  type T = Node
  function Successor(node: T): iset<Reference> { node.children.Values }

  // Stuff for communicating with Disk (probably move to another file?)

  type Superblock = map<Reference, LBA>

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

  datatype Variables = Variables(
      persistentSuperblock: SuperBlock,
      ephemeralSuperblock: SuperBlock,
      cache: map<Reference, CacheLine>);

  datatype Step =
    | WriteBackStep(ref: Reference)
    | WriteBackSuperblockStep
    | DirtyStep(ref: Reference, block: T)
    | PageInStep
    | EvictStep(ref: Reference)
    // TODO unalloc
    // TODO page in superblock

  predicate WriteBack(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && dop.Write?
    && ref in s.cache
    && dop.lba !in persistentSuperblock.Values
    && dop.lba !in ephemeralSuperblock.Values
    && dop.sector == SectorBlock(s.cache[dop.lba].block)
    && s'.persistentSuperblock == s.persistentSuperblock
    && s'.ephemeralSuperblock == s.ephemeralSuperblock[ref := dop.lba]
    && s'.cache == s.cache[ref := s.cache[ref][status := Clean]]
  }

  predicate WriteBackSuperblock(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
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

  predicate PageIn(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && dop.Read
    && ref in s.cache ==> s.cache[ref].status == Clean
    && ref in s.ephemeralSuperblock
    && s.ephemeralSuperblock[ref] == dop.lba
    && dop.sector.SectorBlock?
    && s' == s[cache := s.cache[ref := CacheLine(dop.sector.block, Clean)]]
  }

  predicate Evict(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && dop.NoDiskOp
    && ref in s.cache
    && s.cache[ref].status == Clean
    && s' == s[cache := RemoveFromMap(s.cache, ref)]
  }

  predicate WFSuperblock(superblock: Superblock)
  {
    SuperBlockLBA !in superblock.Values
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && WFSuperblock(s.persistentSuperblock)
    && WFSuperblock(s.ephemeralSuperblock)
    && (forall ref in s.cache.keys :: s.cache.keys[ref].status == Clean ==> ref in s.ephemeralSuperblock)
  }
}
