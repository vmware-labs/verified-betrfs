include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../PivotBetree/Bounds.i.dfy"

module DiskLayout {
  import opened NativeTypes
  import opened Bounds
  import opened Options

  type Addr(==,!new) = uint64
  datatype Location = Location(addr: Addr, len: uint64)

  // Definitions

  function method NumJournalBlocks() : uint64 {
    DiskNumJournalBlocksUint64()
  }

  function method IndirectionTableMaxLength() : uint64 {
    IndirectionTableBlockSizeUint64()
  }

  function method IndirectionTable1Addr() : Addr {
    2 * 4096 + NumJournalBlocks() * 4096
  }

  function method IndirectionTable2Addr() : Addr {
    IndirectionTable1Addr() + IndirectionTableMaxLength()
  }

  function method JournalStartAddr() : uint64
  {
    2 * 4096
  }

  function method JournalEndAddr() : uint64
  {
    JournalStartAddr() + NumJournalBlocks() * 4096
  }

  function method JournalPoint(point: uint64) : uint64
  requires point <= NumJournalBlocks()
  {
    JournalStartAddr() + point * 4096
  }

  // Valididty

  predicate method ValidIndirectionTableAddr(addr: Addr) {
    && (
      || addr == IndirectionTable1Addr()
      || addr == IndirectionTable2Addr()
    )
  }

  predicate method {:opaque} ValidNodeAddr(addr: Addr) {
    //exists j: int :: j * BlockSize() as int == addr as int
    //addr % BlockSize() == 0
    && addr % NodeBlockSizeUint64() == 0
    && addr >= NodeBlockSizeUint64() * MinNodeBlockIndexUint64()
  }

  predicate method {:opaque} ValidJournalLocation(loc: Location) {
    //exists j: int :: addr == 0 <= j < NumJournalBlocks()
    //    && 2 * 4096 + j * 4096
    && loc.addr % 4096 == 0
    && loc.len % 4096 == 0
    && loc.addr >= 2*4096
    && 0 <= (loc.addr - 2*4096) / 4096 < NumJournalBlocks()
    && loc.addr <= 0xffff_ffff_ffff_ffff - loc.len
    && loc.addr + loc.len <= (2 + NumJournalBlocks()) * 4096
  }

  lemma lemma_validJournalBounds(loc: Location)
  ensures ValidJournalLocation(loc) ==>
    && loc.addr >= 2*4096
    && loc.addr as int + loc.len as int <= 
        (2 + NumJournalBlocks() as int) * 4096
  {
    reveal_ValidJournalLocation();
  }

  predicate method ValidIndirectionTableLocation(loc: Location)
  ensures ValidIndirectionTableLocation(loc) ==>
      !ValidJournalLocation(loc)
  {
    lemma_validJournalBounds(loc);

    && ValidIndirectionTableAddr(loc.addr) 
    && 0 < loc.len <= IndirectionTableMaxLength()
  }

  lemma lemma_validNodeAddrBounds(addr: uint64)
  ensures ValidNodeAddr(addr)
      ==> addr >= IndirectionTable2Addr() + IndirectionTableMaxLength()
  {
    reveal_ValidNodeAddr();
  }


  predicate method ValidNodeLocation(loc: Location)
  ensures ValidNodeLocation(loc) ==> !ValidJournalLocation(loc)
  ensures ValidNodeLocation(loc) ==> !ValidIndirectionTableLocation(loc)
  {
    lemma_validJournalBounds(loc);
    lemma_validNodeAddrBounds(loc.addr);

    && ValidNodeAddr(loc.addr)
    && loc.len <= NodeBlockSizeUint64()
  }

  function method Superblock1Location() : Location
  ensures !ValidNodeLocation(Superblock1Location())
  ensures !ValidIndirectionTableLocation(Superblock1Location())
  ensures !ValidJournalLocation(Superblock1Location())
  {
    lemma_validJournalBounds(Location(0, 4096));
    lemma_validNodeAddrBounds(0);

    Location(0, 4096)
  }

  function method Superblock2Location() : Location
  ensures !ValidNodeLocation(Superblock2Location())
  ensures !ValidIndirectionTableLocation(Superblock2Location())
  ensures !ValidJournalLocation(Superblock2Location())
  {
    lemma_validJournalBounds(Location(4096, 4096));
    lemma_validNodeAddrBounds(4096);

    Location(4096, 4096)
  }

  predicate method ValidSuperblock1Location(loc: Location)
  ensures ValidSuperblock1Location(loc) ==> !ValidJournalLocation(loc)
  ensures ValidSuperblock1Location(loc) ==> !ValidIndirectionTableLocation(loc)
  ensures ValidSuperblock1Location(loc) ==> !ValidNodeLocation(loc)
  {
    lemma_validJournalBounds(loc);
    lemma_validNodeAddrBounds(loc.addr);

    loc == Superblock1Location()
  }

  predicate method ValidSuperblock2Location(loc: Location)
  ensures ValidSuperblock2Location(loc) ==> !ValidJournalLocation(loc)
  ensures ValidSuperblock2Location(loc) ==> !ValidIndirectionTableLocation(loc)
  ensures ValidSuperblock2Location(loc) ==> !ValidNodeLocation(loc)
  {
    lemma_validJournalBounds(loc);
    lemma_validNodeAddrBounds(loc.addr);

    loc == Superblock2Location()
  }


  predicate method ValidSuperblockLocation(loc: Location)
  ensures ValidSuperblockLocation(loc) ==>
      (ValidSuperblock1Location(loc) || ValidSuperblock2Location(loc))
  {
    || loc == Superblock1Location()
    || loc == Superblock2Location()
  }

  predicate method ValidLocation(loc: Location)
  {
    || ValidSuperblock1Location(loc)
    || ValidSuperblock2Location(loc)
    || ValidJournalLocation(loc)
    || ValidIndirectionTableLocation(loc)
    || ValidNodeLocation(loc)
  }

  // Lemmas

  lemma ValidNodeAddrDivisor(addr: Addr) returns (i: int)
  requires ValidNodeAddr(addr);
  ensures i * NodeBlockSize() as int == addr as int
  ensures i >= MinNodeBlockIndex()
  {
    reveal_ValidNodeAddr();
    i := addr as int / NodeBlockSize() as int;
  }

  predicate overlap(loc: Location, loc': Location) {
    && loc.addr as int + loc.len as int > loc'.addr as int
    && loc'.addr as int + loc'.len as int > loc.addr as int
  }

  lemma ValidNodeAddrMul(i: uint64)
  requires i as int * NodeBlockSize() as int < 0x1_0000_0000_0000_0000
  requires i as int >= MinNodeBlockIndex()
  ensures ValidNodeAddr(i * NodeBlockSizeUint64())
  {
    reveal_ValidNodeAddr();
  }

  lemma overlappingLocsSameType(loc1: Location, loc2: Location)
  requires ValidLocation(loc1)
  requires ValidLocation(loc2)
  requires overlap(loc1, loc2)
  ensures ValidSuperblock1Location(loc1) <==> ValidSuperblock1Location(loc2)
  ensures ValidSuperblock2Location(loc1) <==> ValidSuperblock2Location(loc2)
  ensures ValidJournalLocation(loc1) <==> ValidJournalLocation(loc2)
  ensures ValidIndirectionTableLocation(loc1) <==> ValidIndirectionTableLocation(loc2)
  ensures ValidNodeLocation(loc1) <==> ValidNodeLocation(loc2)
  {
    lemma_validJournalBounds(loc1);
    lemma_validNodeAddrBounds(loc1.addr);
    lemma_validJournalBounds(loc2);
    lemma_validNodeAddrBounds(loc2.addr);
  }

  lemma overlappingNodesSameAddr(loc1: Location, loc2: Location)
  requires ValidNodeLocation(loc1)
  requires ValidNodeLocation(loc2)
  requires overlap(loc1, loc2)
  ensures loc1.addr == loc2.addr
  {
    reveal_ValidNodeAddr();
  }

  lemma overlappingIndirectionTablesSameAddr(loc1: Location, loc2: Location)
  requires ValidIndirectionTableLocation(loc1)
  requires ValidIndirectionTableLocation(loc2)
  requires overlap(loc1, loc2)
  ensures loc1.addr == loc2.addr
  {
  }

  function method JournalRangeLocation(start: uint64, len: uint64) : (loc : Location)
  requires start < NumJournalBlocks()
  requires start as int + len as int <= NumJournalBlocks() as int
  ensures ValidJournalLocation(loc)
  {
    reveal_ValidJournalLocation();
    Location(JournalPoint(start), len * 4096)
  }

  predicate locContainedInCircularJournalRange(loc: Location, start: uint64, len: uint64)
  requires 0 <= start < NumJournalBlocks()
  requires 0 <= len <= NumJournalBlocks()
  {
    if start + len <= NumJournalBlocks() then (
      && loc.addr >= JournalPoint(start)
      && loc.addr as int + loc.len as int <=
          JournalPoint(start + len) as int
    ) else (
      (
        && loc.addr >= JournalPoint(start)
        && loc.addr as int + loc.len as int <= 
            JournalPoint(NumJournalBlocks()) as int
      ) || (
        && loc.addr >= JournalPoint(0)
        && loc.addr as int + loc.len as int <= 
              JournalPoint(start + len - NumJournalBlocks()) as int
      )
    )
  }

  predicate locDisjointFromCircularJournalRange(loc: Location, start: uint64, len: uint64)
  requires 0 <= start < NumJournalBlocks()
  requires 0 <= len <= NumJournalBlocks()
  {
    if start + len <= NumJournalBlocks() then (
      || loc.addr as int + loc.len as int <= JournalPoint(start) as int
      || loc.addr >= JournalPoint(start + len)
    ) else (
      || (
        loc.addr as int + loc.len as int <= JournalPoint(0) as int
      )
      || (
        loc.addr as int >= JournalPoint(NumJournalBlocks()) as int
      )
      || (
        && loc.addr >= JournalPoint(start + len - NumJournalBlocks())
        && loc.addr as int + loc.len as int <= JournalPoint(start) as int
      )
    )
  }

  function JournalPosAdd(start: int, span: int) : int
  {
    if start + span >= NumJournalBlocks() as int then
      start + span - NumJournalBlocks() as int
    else
      start + span
  }

  function JournalFrontLocation(start: uint64, len: uint64) : Option<Location>
  requires start < NumJournalBlocks()
  {
    if len == 0 then
      None
    else
      Some(JournalRangeLocation(
          start,
          if len <= NumJournalBlocks() - start
          then
            len
          else
            NumJournalBlocks() - start
      ))
  }

  function JournalBackLocation(start: uint64, len: uint64) : Option<Location>
  requires start < NumJournalBlocks()
  requires len <= NumJournalBlocks()
  {
    if len == 0 then
      None
    else if len <= NumJournalBlocks() - start then
      None
    else
      Some(JournalRangeLocation(0, 
          len - (NumJournalBlocks() - start)))
  }

  predicate LocationSub(loc1: Location, loc2: Location)
  {
    && loc1.addr >= loc2.addr
    && loc1.addr as int + loc1.len as int
        <= loc2.addr as int + loc2.len as int
  }

  function {:opaque} JournalBlockIdx(loc: Location) : (i : int)
  requires ValidJournalLocation(loc)
  ensures 0 <= i < NumJournalBlocks() as int
  ensures loc.addr == JournalPoint(i as uint64)
  {
    reveal_ValidJournalLocation();
    (loc.addr as int - (2 * 4096)) / 4096
  }

//~  lemma journalLength1OverlapImpliesContained(start: uint64, loc: Location)
//~  requires 0 <= start < NumJournalBlocks()
//~  requires overlap(JournalRangeLocation(start, 1), loc)
//~  requires ValidLocation(loc)
//~  ensures LocationSub(JournalRangeLocation(start, 1), loc)
//~  {
//~    var block := JournalRangeLocation(start, 1);
//~    overlappingLocsSameType(block, loc);
//~    assert ValidJournalLocation(loc);
//~    reveal_ValidJournalLocation();
//~  }

//~  lemma locDisjointFromCircularJournalRangeOfNonJournalLoc(loc: Location, start: uint64, len: uint64)
//~  requires ValidLocation(loc)
//~  requires !ValidJournalLocation(loc)
//~  requires 0 <= start < NumJournalBlocks()
//~  requires 0 <= len <= NumJournalBlocks()
//~  ensures locDisjointFromCircularJournalRange(loc, start, len)
//~  {
//~    reveal_ValidJournalLocation();
//~    reveal_ValidNodeAddr();
//~  }

//~  lemma ValidJournalLocationConcat(loc1: Location, loc2: Location)
//~  requires ValidJournalLocation(loc1)
//~  requires ValidJournalLocation(loc2)
//~  requires loc1.addr as int + loc1.len as int == loc2.addr as int
//~  ensures loc1.len as int + loc2.len as int < 0x1_0000_0000_0000_0000
//~  ensures ValidJournalLocation(
//~    Location(loc1.addr, loc1.len + loc2.len))
//~  {
//~    reveal_ValidJournalLocation();
//~  }

//~  lemma ValidJournalLocationGetI(loc1: Location, i: int)
//~  requires 0 <= i
//~  requires 4096*(i+1) <= loc1.len as int
//~  requires ValidJournalLocation(loc1)
//~  ensures loc1.addr as int + 4096 * i < 0x1_0000_0000_0000_0000
//~  ensures ValidJournalLocation(Location(loc1.addr + 4096 * i as uint64, 4096))
//~  {
//~    reveal_ValidJournalLocation();
//~  }

  function method otherIndirectionTableAddr(addr: uint64) : uint64
  {
    if addr == IndirectionTable1Addr() then
      IndirectionTable2Addr()
    else
      IndirectionTable1Addr()
  }

  //export S provides LBA, IndirectionTableLBA, toLBA, toUint64, NativeTypes, ValidNodeAddr
  //    reveals BlockSize
  //export extends S
  //export Internal reveals *
}
