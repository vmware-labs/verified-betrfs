#pragma once
#include "BundleWrapper.h"
#include "DafnyRuntime.h"
#include "Framework.h"

using namespace std;

struct ByteString {
  shared_ptr<vector<uint8>> bytes;

  ByteString() { }

  ByteString(std::string const& s)
  {
    bytes = shared_ptr<vector<uint8>>(new vector<uint8>(s.size()));
    for (int i = 0; i < s.size(); i++) {
      (*bytes)[i] = (uint8) s[i];
    }
  }

  ByteString(DafnySequence<uint8> seq)
  {
    bytes = shared_ptr<vector<uint8>>(new vector<uint8>(seq.size()));
    std::copy(seq.ptr(), seq.ptr() + seq.size(), (*bytes).begin());
  }

  std::string as_string() {
    return std::string((char*)&(*bytes)[0], bytes->size());
  }

  DafnySequence<uint8> as_dafny_seq()
  {
    DafnySequence<uint8> s(bytes);
    return s;
  }

  size_t size() {
    return bytes->size();  
  }

  bool operator==(ByteString const& other) const {
    return *bytes == *(other.bytes);
  }

  bool operator<(ByteString const& other) const {
    int m = std::min(bytes->size(), other.bytes->size());
    int c = memcmp(&(*bytes)[0], &(*other.bytes)[0], m);
    if (c < 0) return true;
    if (c > 0) return false;
    return bytes->size() < other.bytes->size();
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
