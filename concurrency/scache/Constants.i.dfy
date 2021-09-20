include "../../lib/Lang/NativeTypes.s.dfy"

module Constants {
  import opened NativeTypes

  const RC_WIDTH: uint64 := 24;
  //const CACHE_SIZE: uint64 := 1048576;
  //const NUM_DISK_PAGES: uint64 := 536870912;

  // Using smaller constants to make small experiments faster
  const CACHE_SIZE: uint64 := 1024;
  const NUM_DISK_PAGES: uint64 := 1000000;

  const CHUNK_SIZE: uint64 := 64;
  const NUM_CHUNKS: uint64 := CACHE_SIZE / 64;
  const CLEAN_AHEAD: uint64 := NUM_CHUNKS / 3;

  const NUM_IO_SLOTS: uint64 := 256;
  const AIO_HAND_BATCH_SIZE: uint64 := 32;

  const DEFAULT_MAX_IO_EVENTS: uint64 := 32;
}
