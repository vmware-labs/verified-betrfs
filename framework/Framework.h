#pragma once

#include "DafnyRuntime.h"

#include <map>
#include <cstring>

namespace KeyType_Compile {
  struct Key {
    uint32_t len;
    uint8_t keydata[20];

    Key() : len(0) { }

    bool operator==(Key const& other) const {
      return len == other.len && memcmp(keydata, other.keydata, len) == 0;
    }

    bool operator!=(Key const& other) const {
      return !(*this == other);
    }
  };

  inline int32_t key__cmp(Key a, Key b) {
    int m = a.len < b.len ? a.len : b.len;
    int c = memcmp(a.keydata, b.keydata, m);
    if (c == 0) {
      return a.len - b.len;
    } else {
      return c;
    }
  }

  inline uint64_t KeyLenUint64(Key a) {
    return a.len;
  }

  inline uint64_t MaxLen() {
    return 20;
  }

  inline Key seq__to__key(DafnySequence<uint8_t> s) {
    Key k;
    k.len = s.size();
    std::copy(s.ptr(), s.ptr() + s.size(), k.keydata);
    return k;
  }

  inline DafnySequence<uint8_t> key__to__seq(Key const& key) {
    DafnySequence<uint8_t> s(key.len);
    std::copy(key.keydata, key.keydata + key.len, s.ptr());
    return s;
  }

  class __default {
    public:
    static void CopyKeyIntoArray(
      Key src,
      DafnyArray<uint8_t> dst,
      uint64 dstIndex)
    {
      std::copy(src.keydata, src.keydata + src.len,
          dst.begin() + dstIndex);
    }
  };

  static_assert(sizeof(Key) == 24, "eh");
}

using KeyType_Compile::Key;

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

template <>
struct std::hash<Key> {
    size_t operator()(const Key& s) const {
        size_t seed = 0;
        for (size_t i = 0; i < s.len; i++) {      
            hash_combine<uint8_t>(seed, s.keydata[i]);
        }
        return seed; 
    }
};

template<>
struct get_default<Key> {
  static Key call() { return Key(); }
};


void ClearIfExists();
void Mkfs();
