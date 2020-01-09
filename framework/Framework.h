#pragma once

#include "DafnyRuntime.h"

#include <map>
#include <cstring>

namespace Maps_Compile {
  class __default {
    public:
    template <typename K, typename V>
    static DafnyMap<K, V> ComputeMapRemove1(DafnyMap<K, V> m, K key)
    {
      DafnyMap<K, V> dm(m);
      dm.map.erase(key);
      return dm;
    }
  };
}

namespace NativeArrays_Compile {
  class __default {
    public:
    static int32_t ByteSeqCmpByteSeq(DafnySequence<uint8> b1, DafnySequence<uint8> b2)
    {
      int result = memcmp(b1.ptr(), b2.ptr(), b1.size() < b2.size() ? b1.size() : b2.size());
      if (result == 0) {
        if (b1.size() == b2.size()) {
          return 0;
        } else if (b1.size() > b2.size()) {
          return 1;
        } else {
          return -1;
        }
      } else {
        return result;
      }
    }

    template <typename T>
    static DafnyArray<T> newArrayFill(uint64 len, T val)
    {
      DafnyArray<T> ar(len);
      for (int i = 0; i < len; i++) {
        ar.at(i) = val;
      }
      return ar;
    }

    template <typename T>
    static DafnyArray<T> newArrayClone(DafnyArray<T> ar)
    {
      shared_ptr<vector<T>> clone { new vector<T>(*ar.vec) };
      DafnyArray<T> clone_ar;
      clone_ar.vec = clone;
      return clone_ar;
    }

    template <typename T>
    static void CopySeqIntoArray(
      DafnySequence<T> src,
      uint64 srcIndex,
      DafnyArray<T> dst,
      uint64 dstIndex,
      uint64 len)
    {
      std::copy(src.ptr() + srcIndex, src.ptr() + (srcIndex + len),
          dst.begin() + dstIndex);
    }
  };
}

namespace Crypto_Compile {
  class __default {
    public:
    static DafnySequence<uint8> Sha256(DafnySequence<uint8>);
    static DafnySequence<uint8> Crc32C(DafnySequence<uint8>);
    static DafnySequence<uint8> Crc32CArray(DafnyArray<uint8>, uint64 start, uint64 len);
  };
}

namespace MainDiskIOHandler_Compile {
  struct ReadTask;
  struct WriteTask;

  class DiskIOHandler {
    public:
    uint64 write(uint64 addr, DafnyArray<uint8> bytes);
    uint64 read(uint64 addr, uint64 len);
    uint64 getWriteResult();
    Tuple2<uint64, DafnySequence<uint8>> getReadResult();

    DiskIOHandler();
    bool prepareWriteResponse();
    bool prepareReadResponse();

    private:
    uint64 readResponseId;
    DafnySequence<uint8> readResponseBytes;

    uint64 writeResponseId;

    uint64 curId;

    std::map<uint64, WriteTask> writeReqs;
    std::map<uint64, ReadTask> readReqs;
  };
}

void ClearIfExists();
void Mkfs();
