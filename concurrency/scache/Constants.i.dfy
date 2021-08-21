include "../../lib/Lang/NativeTypes.s.dfy"

module Constants {
  import opened NativeTypes

  const NUM_THREADS := 24;
  const CACHE_SIZE := 1048576;
  const NUM_DISK_PAGES := 536870912;

  const CHUNK_SIZE := 64;
  const NUM_CHUNKS := CACHE_SIZE / 64;
  const CLEAN_AHEAD := NUM_CHUNKS / 3;

  const NUM_IO_SLOTS := 128;

  const DEFAULT_MAX_IO_EVENTS: uint64 := 32;
}
