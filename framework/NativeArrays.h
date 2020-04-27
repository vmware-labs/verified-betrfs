#pragma once

#include "DafnyRuntime.h"

namespace NativeArrays_Compile {
  int32_t ByteSeqCmpByteSeq(DafnySequence<uint8> b1, DafnySequence<uint8> b2);
  
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


