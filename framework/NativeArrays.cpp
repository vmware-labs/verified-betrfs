#include "NativeArrays.h"

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
}


