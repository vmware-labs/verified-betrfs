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
      for (size_t i = 0; i < len; i++) {
        ar.at(i) = val;
      }
      return ar;
    }

    template <typename T>
    static DafnyArray<T> newArrayClone(DafnyArray<T> ar)
    {
      DafnyArray<T> clone_ar(ar.size());
      std::copy(ar.begin(), ar.end(), clone_ar.begin());
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

    template <typename T>
    static void CopyArrayIntoDifferentArray(
      DafnyArray<T> src,
      uint64 srcIndex,
      DafnyArray<T> dst,
      uint64 dstIndex,
      uint64 len)
    {
      // We're allowed to do this without checking the ranges overlap
      // because CopyArrayIntoDifferentArray has the condition
      // src != dst.
      std::copy(src.begin() + srcIndex, src.begin() + (srcIndex + len),
          dst.begin() + dstIndex);
    }
  };
}

namespace NativePackedInts_Compile {
  static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, "current implementation of NativePackedInts assumes little endian");
  static_assert(sizeof(uint32) == 4, "uint32 is aliased wrong");
  static_assert(sizeof(uint64) == 8, "uint64 is aliased wrong");

  class __default {
    public:
    static uint32 Unpack__LittleEndian__Uint32(DafnySequence<uint8> const& packed, uint64 idx)
    {
      uint32 res;
      memcpy(&res, packed.ptr() + idx, sizeof(uint32));
      return res;
    }

    static uint64 Unpack__LittleEndian__Uint64(DafnySequence<uint8> const& packed, uint64 idx)
    {
      uint64 res;
      memcpy(&res, packed.ptr() + idx, sizeof(uint64));
      return res;
    }

    static void Pack__LittleEndian__Uint32__into__Array(uint32 i, DafnyArray<uint8> const& ar, uint64 idx)
    {
      memcpy(&ar.at(idx), &i, sizeof(uint32));
    }

    static void Pack__LittleEndian__Uint64__into__Array(uint64 i, DafnyArray<uint8> const& ar, uint64 idx)
    {
      memcpy(&ar.at(idx), &i, sizeof(uint64));
    }

    static DafnySequence<uint32> Unpack__LittleEndian__Uint32__Seq(DafnySequence<uint8> const& packed, uint64 idx, uint64 len)
    {
      // TODO is there a safe way to do this without a copy?
      DafnySequence<uint32> res(len);
      memcpy(res.ptr(), packed.ptr() + idx, sizeof(uint32) * len);
      return res;
    }

    static DafnySequence<uint64> Unpack__LittleEndian__Uint64__Seq(DafnySequence<uint8> const& packed, uint64 idx, uint64 len)
    {
      DafnySequence<uint64> res(len);
      memcpy(res.ptr(), packed.ptr() + idx, sizeof(uint64) * len);
      return res;
    }

    static void Pack__LittleEndian__Uint32__Seq__into__Array(DafnySequence<uint32> const& unpacked, DafnyArray<uint8> const& ar, uint64 idx)
    {
      memcpy(&ar.at(idx), unpacked.ptr(), sizeof(uint32) * unpacked.size());
    }

    static void Pack__LittleEndian__Uint64__Seq__into__Array(DafnySequence<uint64> const& unpacked, DafnyArray<uint8> const& ar, uint64 idx)
    {
      memcpy(&ar.at(idx), unpacked.ptr(), sizeof(uint64) * unpacked.size());
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
    void completeWriteTasks();
    void waitForOne();
    void maybeStartWriteReq();

    private:
    uint64 readResponseId;
    DafnySequence<uint8> readResponseBytes;

    uint64 writeResponseId;

    uint64 curId;

    std::map<uint64, std::shared_ptr<WriteTask>> writeReqs;
    std::map<uint64, ReadTask> readReqs;
  };
}

namespace NativeBenchmarking_Compile {
  class __default {
  public:
    static void start(DafnySequence<char> dafnyName);
    static void end(DafnySequence<char> dafnyName);
  };
}

void ClearIfExists();
void Mkfs();
