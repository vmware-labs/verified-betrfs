#pragma once
#include "BundleWrapper.h"
#include "DafnyRuntime.h"
#include "Framework.h"

struct ByteString {
  DafnySequence<uint8> seq;

  ByteString() { }

  explicit ByteString(int n) : seq(n) { }
  explicit ByteString(DafnySequence<uint8> seq) : seq(seq) { }

  explicit ByteString(std::string const& s) : seq(s.size()) {
    uint8* ptr = (uint8*) &s[0];
    std::copy(ptr, ptr + size(), seq.ptr());
  }

  std::string as_string() {
    return std::string((char *)seq.ptr(), seq.size());
  }

  DafnySequence<uint8> as_dafny_seq()
  {
    return seq;
  }

  size_t size() const {
    return seq.size();  
  }

  bool operator==(ByteString const& other) const {
    return seq.equals(other.seq);
  }

  bool operator<(ByteString const& other) const {
    int m = std::min(seq.size(), other.seq.size());
    int c = memcmp(seq.ptr(), other.seq.ptr(), m);
    if (c < 0) return true;
    if (c > 0) return false;
    return seq.size() < other.seq.size();
  }
};

class Application {
public:
  Application(std::string filename);
  void initialize();
  void crash();

  void Insert(std::string const& key, std::string const& val);
  ByteString Query(std::string const& key);

  void Sync();
  void Insert(ByteString key, ByteString val);
  ByteString Query(ByteString key);
  void QueryAndExpect(ByteString key, ByteString expected_val);
  std::vector<std::pair<ByteString, ByteString>> Succ(
      ByteString lowerBound, bool inclusive, uint64 targetCount);

private:
  Constants k;
  Variables hs;
  std::string filename;
  std::shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io;

  bool maybeDoResponse();
  void log(std::string const&);

  UI_Compile::SuccResultList SuccOnce(UI_Compile::RangeStart start, uint64 maxToFind);
};
