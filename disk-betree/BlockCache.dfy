

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
      cache: map<LBA, CacheLine>);

  datatype Step =
    | WriteBackStep
    | WriteBackSuperblockStep
    | DirtyStep(Reference, T)
    | AllocStep(Reference, T, LBA)
    | PageInStep
    | EvictStep(lba: LBA)
    // TODO unalloc
    // TODO page in superblock

  predicate WriteBack(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    // TODO allocate new lba
    && dop.Write?
    && dop.lba in s.cache
    && dop.sector == SectorBlock(s.cache[dop.lba].block)
    && s' == s[cache := s.cache[dop.lba := s.cache[dop.lba][status := Clean]]]
  }

  predicate WriteBackSuperblock(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.Write?
    && dop.lba == SuperblockLBA(k)
    && dop.sector == SectorSuperblock(s.ephemeralSuperblock)
    && (forall cacheLine :: cacheLine in s.cache.Values ==> cacheLine.stauts == Clean)
    && s' == s[persistentSuperblock := s.ephemeralSuperblock]
  }

  predicate Dirty(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference, block: T)
  {
    && dop.NoDiskOp
    && ref in s.ephemeralSuperblock
    && var lba := s.ephemeralSuperblock[ref]
    && s' == s[cache := s.cache[lba := CacheLine(block, Dirty)]]
  }

  predicate Alloc(k: Constants, s: Variables: s': Variables, dop: DiskOp, ref: Reference, block: T, lba: LBA)
  {
    && dop.NoDiskOp
    && lba !in s.ephemeralSuperblock.Values
    && lba !in s.persistentSuperblock.Values
    && ref !in s.ephemeralSuperblock
    && s'.
  }

  predicate PageIn(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.Read
    && dop.lba in s.cache ==> s.cache[dop.lba].status == Clean
    && dop.lba in s.ephemeralSuperblock.Values
    && dop.sector.SectorBlock?
    && s' == s[cache := s.cache[dop.lba := CacheLine(dop.sector.block, Clean)]]
  }

  predicate Evict(k: Constants, s: Variables, s': Variables, dop: DiskOp, lba: LBA)
  {
    && dop.NoDiskOp
    && lba in s.cache
    && s.cache[lba].status == Clean
    && s' == s[cache := RemoveFromMap(s.cache, lba)]
  }

  predicate WFSuperblock(superblock: Superblock)
  {
    SuperBlockLBA !in superblock.Values
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && WFSuperblock(s.persistentSuperblock)
    && WFSuperblock(s.ephemeralSuperblock)
    && (s.cache.keys <= s.ephemeralSuperblock.Values)
  }
}
