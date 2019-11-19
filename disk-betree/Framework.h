#include "DafnyRuntime.h"

namespace NativeArrays_Compile {
  int32_t ByteSeqCmpByteSeq(DafnySequence<uint8>, DafnySequence<uint8>);

  template <typename T>
  shared_ptr<vector<T>> newArrayFill(uint64, T);

  template <typename T>
  shared_ptr<vector<T>> newArrayClone(uint64, shared_ptr<vector<T>>);

  template <typename T>
  void CopySeqIntoArray(
    DafnySequence<T> src,
    uint64 srcIndex,
    shared_ptr<vector<T>> dst,
    uint64 dstIndex,
    uint64 len);
}

namespace Crypto_Compile {
  DafnySequence<uint8> Crc32CArray(shared_ptr<vector<uint8>>, uint64 start, uint64 len);
}
