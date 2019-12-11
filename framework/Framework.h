#pragma once

#include "DafnyRuntime.h"

namespace Maps_Compile {
  class __default {
    public:
    template <typename K, typename V>
    static DafnyMap<K, V> ComputeMapRemove1(DafnyMap<K, V>, K);
  };
}

namespace NativeArrays_Compile {
  class __default {
    public:
    static int32_t ByteSeqCmpByteSeq(DafnySequence<uint8>, DafnySequence<uint8>);

    template <typename T>
    static shared_ptr<vector<T>> newArrayFill(uint64, T);

    template <typename T>
    static shared_ptr<vector<T>> newArrayClone(shared_ptr<vector<T>>);

    template <typename T>
    static void CopySeqIntoArray(
      DafnySequence<T> src,
      uint64 srcIndex,
      shared_ptr<vector<T>> dst,
      uint64 dstIndex,
      uint64 len);
  };
}

namespace Crypto_Compile {
  class __default {
    public:
    static DafnySequence<uint8> Sha256(DafnySequence<uint8>);
    static DafnySequence<uint8> Crc32C(DafnySequence<uint8>);
    static DafnySequence<uint8> Crc32CArray(shared_ptr<vector<uint8>>, uint64 start, uint64 len);
  };
}

namespace MainDiskIOHandler_Compile {
  class DiskIOHandler {
    public:
    uint64 write(uint64 addr, shared_ptr<vector<uint8>> bytes);
    uint64 read(uint64 addr, uint64 len);
    uint64 getWriteResult();
    Tuple2<uint64, DafnySequence<uint8>> getReadResult();
  };
}
