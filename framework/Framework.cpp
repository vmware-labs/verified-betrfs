#include "Framework.h"

#include "Crc32.h"

typedef uint8 byte;

namespace Maps_Compile {
  template <typename K, typename V>
  DafnyMap<K, V> __default::ComputeMapRemove1(DafnyMap<K, V> m, K key)
  {
    DafnyMap<K, V> dm(m);
    dm.map.erase(key);
    return dm;
  }
}

namespace NativeArrays_Compile {
  int32_t __default::ByteSeqCmpByteSeq(
      DafnySequence<byte> b1,
      DafnySequence<byte> b2)
  {
    int result = memcmp(&b1.seq[0], &b2.seq[0], b1.seq.size() < b2.seq.size() ? b1.seq.size() : b2.seq.size());
    if (result == 0) {
      if (b1.seq.size() == b2.seq.size()) {
        return 0;
      } else if (b1.seq.size() > b2.seq.size()) {
        return 1;
      } else {
        return -1;
      }
    } else {
      return result;
    }
  }

  template <typename T>
  shared_ptr<vector<T>> __default::newArrayFill(uint64 len, T val)
  {
    shared_ptr<vector<T>> ar { new vector<T>(len) };
    for (int i = 0; i < len; i++) {
      (*ar)[i] = val;
    }
  }

  template <typename T>
  shared_ptr<vector<T>> __default::newArrayClone(shared_ptr<vector<T>> ar)
  {
    shared_ptr<vector<T>> clone { new vector<T>(ar) };
    return clone;
  }
}

namespace Crypto_Compile {
  DafnySequence<byte> padded_crc32(byte* bytes, int len)
  {
    uint32_t crc = crc32c(bytes, len);

    DafnySequence<byte> padded;
    padded.seq.resize(32);
    padded.update(0, (uint8_t)(crc & 0xff));
    padded.update(1, (uint8_t)((crc >> 8) & 0xff));
    padded.update(2, (uint8_t)((crc >> 16) & 0xff));
    padded.update(3, (uint8_t)((crc >> 24) & 0xff));
    for (int i = 4; i < 32; i++) {
      padded.update(i, 0);
    }

    return padded;
  }
}
