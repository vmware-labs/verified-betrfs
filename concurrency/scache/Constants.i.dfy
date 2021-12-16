include "../../lib/Lang/NativeTypes.s.dfy"

module Constants {
  import opened NativeTypes

  ghost const RC_WIDTH := 4;
  //const CACHE_SIZE := 1048576;
  //const NUM_DISK_PAGES := 536870912;

  // Using smaller constants to make small experiments faster
  ghost const CACHE_SIZE := 131072;
  ghost const NUM_DISK_PAGES := 7864320;

  ghost const CHUNK_SIZE := 64;
  ghost const NUM_CHUNKS := CACHE_SIZE / 64;
  ghost const CLEAN_AHEAD := 512;

  ghost const NUM_IO_SLOTS := 256;
  ghost const AIO_HAND_BATCH_SIZE := 32;

  ghost const PAGES_PER_EXTENT := 32;

  function method CACHE_SIZE_64(): uint64 { 131072 }
  function method NUM_DISK_PAGES_64(): uint64 { 7864320 }
  function method AIO_HAND_BATCH_SIZE_64(): uint64 { 32 }
  function method NUM_IO_SLOTS_64(): uint64 { 256 }
  function method PAGES_PER_EXTENT_64(): uint64 { 32 }
  function method CHUNK_SIZE_32(): uint32 { 64 }
  function method DEFAULT_MAX_IO_EVENTS_64(): uint64 { 32 }
  function method RC_WIDTH_64(): uint64 { 4 }
  function method NUM_CHUNKS_64(): uint64 { CACHE_SIZE_64() / 64 }
  function method CLEAN_AHEAD_64(): uint64 { 512 }

  function method PLATFORM_CACHELINE_SIZE_64(): uint64 { 64 }

  function CACHELINE_CAPACITY() : int
  ensures CACHELINE_CAPACITY() == CACHE_SIZE / PLATFORM_CACHELINE_SIZE_64() as int
  { 2048 }
}
