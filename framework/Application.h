#pragma once
#include "BundleWrapper.h"
#include "DafnyRuntime.h"
#include "Framework.h"

using namespace std;

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

  size_t size() {
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
  Application();
  void log(std::string const&);
  void initialize();
  void crash();

  void Insert(string const& key, string const& val);
  ByteString Query(string const& key);

  void Sync();
  void Insert(ByteString key, ByteString val);
  ByteString Query(ByteString key);
  void QueryAndExpect(ByteString key, ByteString expected_val);
  bool maybeDoResponse();

private:
  Constants k;
  Variables hs;
  shared_ptr<MainDiskIOHandler_Compile::DiskIOHandler> io;
};
