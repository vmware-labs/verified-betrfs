include "../lib/Base/NativeTypes.s.dfy"
include "../PivotBetree/Bounds.i.dfy"

module DiskLayout {
  import opened NativeTypes
  import opened Bounds

  type Addr(==,!new) = uint64
  datatype Location = Location(addr: Addr, len: uint64)

  // Definitions

  function method Superblock1Location() : Location {
    Location(0, 4096)
  }

  function method Superblock2Location() : Location {
    Location(4096, 4096)
  }

  function method NumJournalBlocks() : uint64 {
    2048
  }

  function method IndirectionTableMaxLength() : uint64 {
    24 * 1024 * 1024
  }

  function method IndirectionTable1Addr() : Addr {
    2 * 4096 + NumJournalBlocks() * 4096
  }

  function method IndirectionTable2Addr() : Addr {
    IndirectionTable1Addr() + IndirectionTableMaxLength()
  }

  function method JournalRangeLocation(start: uint64, len: uint64) : Location
  requires start < NumJournalBlocks()
  requires start as int + len as int <= NumJournalBlocks() as int
  {
    Location(2 * 4096 + start * 4096,
             2 * 4096 + (start + len) * 4096)
  }

  // Valididty

  predicate method ValidIndirectionTableAddr(addr: Addr) {
    && (
      || addr == 2 * 1024
      || addr == 2 * 1024 + IndirectionTableMaxLength()
    )
  }

  predicate method {:opaque} ValidNodeAddr(addr: Addr) {
    //exists j: int :: j * BlockSize() as int == addr as int
    //addr % BlockSize() == 0
    && addr % NodeBlockSizeUint64() == 0
    && addr >= NodeBlockSizeUint64() * MinNodeBlockIndexUint64()
  }

  predicate method ValidIndirectionTableLocation(loc: Location) {
    && ValidIndirectionTableAddr(loc.addr) 
    && loc.len <= IndirectionTableMaxLength()
  }

  predicate method ValidNodeLocation(loc: Location) {
    && ValidNodeAddr(loc.addr)
    && loc.len <= NodeBlockSizeUint64()
  }

  predicate method ValidSuperblock1Location(loc: Location) {
    loc == Superblock1Location()
  }

  predicate method ValidSuperblock2Location(loc: Location) {
    loc == Superblock2Location()
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
    loc.addr == loc'.addr
  }

  lemma ValidNodeAddrMul(i: uint64)
  requires i as int * NodeBlockSize() as int < 0x1_0000_0000_0000_0000
  requires i as int >= MinNodeBlockIndex()
  ensures ValidNodeAddr(i * NodeBlockSizeUint64())
  {
    reveal_ValidNodeAddr();
  }

  lemma ValidNodeAddr0()
  ensures ValidNodeAddr(0)
  {
    reveal_ValidNodeAddr();
  }

  //export S provides LBA, IndirectionTableLBA, toLBA, toUint64, NativeTypes, ValidNodeAddr
  //    reveals BlockSize
  //export extends S
  //export Internal reveals *
}
