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
