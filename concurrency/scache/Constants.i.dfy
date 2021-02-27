// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

module Constants {
  const NUM_THREADS := 24;
  const CACHE_SIZE := 1048576;
  const NUM_DISK_PAGES := 536870912;

  const CHUNK_SIZE := 64;
  const NUM_CHUNKS := CACHE_SIZE / 64;
  const CLEAN_AHEAD := NUM_CHUNKS / 3;

  const NUM_IO_SLOTS := 128;
}
