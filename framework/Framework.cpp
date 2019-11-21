typedef uint8_t byte;

namespace TotalOrderNative_Compile {
  int32_t Arrays::ByteSeqCmpByteSeq(
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
}

namespace Crypto_Compile {
  class __default {
    DafnySequence<byte> padded_crc32(byte* bytes, int len)
    {
      uint32_t crc = crc32c(bytes, len);

      DafnySequence<byte> padded;
      padded.seq.resize(32);
      padded[0] = (uint8_t)(crc & 0xff);
      padded[1] = (uint8_t)((crc >> 8) & 0xff);
      padded[2] = (uint8_t)((crc >> 16) & 0xff);
      padded[0] = (uint8_t)((crc >> 24) & 0xff);
      for (int i = 4; i < 32; i++) {
        padded[i] = 0;
      }

      return padded;
    }
  }
}
