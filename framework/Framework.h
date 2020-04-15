#pragma once

#include "DafnyRuntime.h"
#include "MallocAccounting.h"

#include <map>
#include <unordered_map>
#include <cstring>

namespace Maps_Compile {
  template <typename K, typename V>
  DafnyMap<K, V> ComputeMapRemove1(DafnyMap<K, V> m, K key)
  {
    DafnyMap<K, V> dm(m);
    dm.map.erase(key);
    return dm;
  }
}

namespace NativeArithmetic_Compile {
  uint64_t u64add(uint64_t a, uint64_t b);
}

namespace NativeArrays_Compile {
  int32_t ByteSeqCmpByteSeq(DafnySequence<uint8> b1, DafnySequence<uint8> b2)
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
  DafnyArray<T> newArrayFill(uint64 len, T val)
  {
    DafnyArray<T> ar(len);
    for (size_t i = 0; i < len; i++) {
      ar.at(i) = val;
    }
    return ar;
  }

  template <typename T>
  DafnyArray<T> newArrayClone(DafnyArray<T> ar)
  {
    DafnyArray<T> clone_ar(ar.size());
    std::copy(ar.begin(), ar.end(), clone_ar.begin());
    return clone_ar;
  }

  template <typename T>
  void CopySeqIntoArray(
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
  void CopyArrayIntoDifferentArray(
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
}

namespace NativePackedInts_Compile {
  static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, "current implementation of NativePackedInts assumes little endian");
  static_assert(sizeof(uint32) == 4, "uint32 is aliased wrong");
  static_assert(sizeof(uint64) == 8, "uint64 is aliased wrong");

  uint32 Unpack__LittleEndian__Uint32(DafnySequence<uint8> const& packed, uint64 idx);
  uint64 Unpack__LittleEndian__Uint64(DafnySequence<uint8> const& packed, uint64 idx);
  void Pack__LittleEndian__Uint32__into__Array(uint32 i, DafnyArray<uint8> const& ar, uint64 idx);
  void Pack__LittleEndian__Uint64__into__Array(uint64 i, DafnyArray<uint8> const& ar, uint64 idx);
  DafnySequence<uint32> Unpack__LittleEndian__Uint32__Seq(DafnySequence<uint8> const& packed, uint64 idx, uint64 len);
  DafnySequence<uint64> Unpack__LittleEndian__Uint64__Seq(DafnySequence<uint8> const& packed, uint64 idx, uint64 len);
  void Pack__LittleEndian__Uint32__Seq__into__Array(DafnySequence<uint32> const& unpacked, DafnyArray<uint8> const& ar, uint64 idx);
  void Pack__LittleEndian__Uint64__Seq__into__Array(DafnySequence<uint64> const& unpacked, DafnyArray<uint8> const& ar, uint64 idx);
}

namespace Crypto_Compile {
  DafnySequence<uint8> Sha256(DafnySequence<uint8>);
  DafnySequence<uint8> Crc32C(DafnySequence<uint8>);
  DafnySequence<uint8> Crc32CArray(DafnyArray<uint8>, uint64 start, uint64 len);
}

namespace MainDiskIOHandler_Compile {
  struct ReadTask;
  struct WriteTask;

  class DiskIOHandler {
    public:
    uint64 write(uint64 addr, DafnySequence<uint8> bytes);
    Tuple2<uint64, uint64> write2(
      uint64 addr1, DafnySequence<uint8> bytes1,
      uint64 addr2, DafnySequence<uint8> bytes2);
    uint64 read(uint64 addr, uint64 len);
    Tuple3<uint64, uint64, uint64> getWriteResult();
    Tuple3<uint64, uint64, DafnySequence<uint8>> getReadResult();

    DiskIOHandler(std::string filename = ".veribetrfs.img");
    ~DiskIOHandler();
    bool prepareWriteResponse();
    bool prepareReadResponse();
    void completeWriteTasks();
    void waitForOne();
    void maybeStartWriteReq();

    bool has_read_task() { return !readReqs.empty(); }
    bool has_write_task() { return !writeReqs.empty(); }

    private:
    int fd;
    
    uint64 readResponseId;
    DafnySequence<uint8> readResponseBytes;

    uint64 writeResponseId;
    uint64 responseAddr;
    uint64 responseLen;

    uint64 curId;

    std::map<uint64, std::shared_ptr<WriteTask>> writeReqs;
    std::map<uint64, ReadTask> readReqs;
  };
}

namespace NativeBenchmarking_Compile {
  void start(DafnySequence<char> dafnyName);
  void end(DafnySequence<char> dafnyName);
}

namespace MallocAccounting_Compile {
  void set_amass_mode(bool b);
}

namespace NodeImpl_Compile {
class Node;
}

namespace AllocationReport_Compile {
  void start();
  void sampleNode(uint64 ref, std::shared_ptr<NodeImpl_Compile::Node> node);
  void stop();
}

void benchmark_start(std::string const&);
void benchmark_end(std::string const&);
void benchmark_append(std::string const&, long long ns);
void benchmark_clear();
void benchmark_dump();

void Mkfs(std::string filename = ".veribetrfs.img");
