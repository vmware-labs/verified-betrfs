// Needs to be compiled with -msse4.2

#include <iostream>
#include <cstring>
#include <smmintrin.h>
#include "DafnyRuntime.h"
#include "Framework.h"

using namespace std;

uint32_t crc32c(const uint8_t *bytes, size_t len)
{
  uint32_t acc = 0xffffffff;

  while (((uintptr_t)bytes) & 0x7 && len > 0) {
    acc = _mm_crc32_u8(acc, *bytes);
    bytes++;
    len--;
  }

  while (len >= 8) {
    acc = _mm_crc32_u64(acc, *((const uint64_t *)bytes));
    len -= 8;
    bytes += 8;
  }

  if (len >= 4) {
    acc = _mm_crc32_u32(acc, *((const uint32_t *)bytes));
    len -= 4;
    bytes += 4;
  }

  if (len >= 2) {
    acc = _mm_crc32_u16(acc, *((const uint16_t *)bytes));
    len -= 2;
    bytes += 2;
  }

  if (len >= 1) {
    acc = _mm_crc32_u8(acc, *bytes);
    len -= 1;
    bytes += 1;
  }

  return ~acc;
}

typedef uint8 byte;

namespace Crypto_Compile {
  DafnySequence<byte> padded_crc32(byte* bytes, int len)
  {
    uint32_t crc = crc32c(bytes, len);

    DafnySequence<byte> padded(32);
    padded.ptr()[0] = (uint8_t)(crc & 0xff);
    padded.ptr()[1] = (uint8_t)((crc >> 8) & 0xff);
    padded.ptr()[2] = (uint8_t)((crc >> 16) & 0xff);
    padded.ptr()[3] = (uint8_t)((crc >> 24) & 0xff);
    for (int i = 4; i < 32; i++) {
      padded.ptr()[i] = 0;
    }

    return padded;
  }

  DafnySequence<uint8> __default::Crc32C(DafnySequence<uint8> bytes)
  {
    return padded_crc32(bytes.ptr(), bytes.size());
  }

  DafnySequence<uint8> __default::Crc32CArray(DafnyArray<uint8> bytes, uint64 start, uint64 len)
  {
    return padded_crc32(&bytes.at(start), len);
  }
}

/*int main() {
  const char* ch = "The quick brown fox jumps over the lazy dog";
  cout << crc32c((const uint8_t*)ch, strlen(ch)) << endl;
}*/
