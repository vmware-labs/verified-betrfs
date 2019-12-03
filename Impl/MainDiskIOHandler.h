#pragma once

#include "DafnyRuntime.h"

namespace MainDiskIOHandler {
  class DiskIOHandler {
    uint64 write(uint64 addr, shared_ptr<vector<uint8>> bytes);
    uint64 read(uint64 addr, uint64 len);
    uint64 getWriteResult();
    Tuple2<uint64, DafnySequence<uint8>> getReadResult();
  };
}
