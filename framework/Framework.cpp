#include "BundleWrapper.h"
#include "Application.h"

//#include <filesystem> // c++17 lol
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>

[[ noreturn ]]
void fail(string err)
{
  cout << "fatal error: " << err << endl;
  exit(1);
}

typedef uint8 byte;

namespace MainDiskIOHandler_Compile {
  constexpr int BLOCK_SIZE = 8*1024*1024;

  struct WriteTask { };

  struct ReadTask {
    shared_ptr<vector<byte>> bytes;

    ReadTask(shared_ptr<vector<byte>> s) : bytes(s) { }
  };

  string getFilename(uint64 addr) {
    // Convert to hex
    char num[17];
    for (int i = 0; i < 16; i++) {
      int digit = (addr >> (4 * i)) & 0xf;
      num[15 - i] = (digit < 10 ? '0' + digit : 'a' + digit - 10);
    }
    num[16] = '\0';
    return ".veribetrfs-storage/" + string(num);
  }

  int readFile(string const& filename, byte* res, int len)
  {
    FILE* f = fopen(filename.c_str(), "r");
    if (f == NULL) {
      fail("read fopen failed");
    }

    int count = fread(res, 1, len, f);
    if (ferror(f) != 0) {
      fail("fread failed");
    }
    
    int close_res = fclose(f);
    if (close_res != 0) {
      fail("read fclose failed");
    }

    return count;
  }

  void writeSync(uint64 addr, byte* sector, int len) {
    if (len > BLOCK_SIZE || addr % BLOCK_SIZE != 0) {
      fail("writeSync not implemented for these arguments");
    }

    FILE* f = fopen(getFilename(addr).c_str(), "w");
    if (f == NULL) {
      fail("write fopen failed");
    }

    size_t res = fwrite(sector, 1, len, f);
    if (res != len) {
      fail("fwrite failed");
    }

    int flush_res = fflush(f);
    if (flush_res != 0) {
      fail("fflush failed");
    }

    int close_res = fclose(f);
    if (close_res != 0) {
      fail("write fclose failed");
    }
  }

  void readSync(uint64 addr, uint64 len, byte* sector) {
    if (addr % BLOCK_SIZE != 0 || len > BLOCK_SIZE) {
      fail("readSync not implemented for these arguments");
    }

    string filename = getFilename(addr);
    int actualRead = readFile(filename, sector, len);
    if ((uint64)actualRead < len) {
      fail("readSync did not find enough bytes");
    }
  }

  DiskIOHandler::DiskIOHandler() : curId(0) { }

  uint64 DiskIOHandler::write(uint64 addr, shared_ptr<vector<uint8>> bytes)
  {
    writeSync(addr, &(*bytes)[0], (*bytes).size());

    uint64 id = this->curId;
    this->curId++;

    writeReqs.insert(make_pair(id, WriteTask()));

    return id;
  }

  uint64 DiskIOHandler::read(uint64 addr, uint64 len)
  {
    shared_ptr<vector<byte>> bytes { new vector<byte>(len) };
    readSync(addr, len, &(*bytes)[0]);

    uint64 id = this->curId;
    this->curId++;

    readReqs.insert(make_pair(id, ReadTask(bytes)));

    return id;
  }

  uint64 DiskIOHandler::getWriteResult()
  {
    return writeResponseId;
  }

  Tuple2<uint64, DafnySequence<uint8>> DiskIOHandler::getReadResult()
  {
    return Tuple2<uint64, DafnySequence<uint8>>(readResponseId, readResponseBytes);
  }

  bool DiskIOHandler::prepareReadResponse() {
    auto it = this->readReqs.begin();
    if (it != this->readReqs.end()) {
      this->readResponseId = it->first;
      this->readResponseBytes = DafnySequence<uint8>(it->second.bytes);
      this->readReqs.erase(it);
      return true;
    } else {
      return false;
    }
  }

  bool DiskIOHandler::prepareWriteResponse() {
    auto it = this->writeReqs.begin();
    if (it != this->writeReqs.end()) {
      this->writeResponseId = it->first;
      this->writeReqs.erase(it);
      return true;
    } else {
      return false;
    }
  }
}

using MainDiskIOHandler_Compile::DiskIOHandler;

#ifdef VERBOSE
  #define LOG log
#else
  #define LOG(x)
#endif

Application::Application() {
  initialize();
}

void Application::initialize() {
  auto tup2 = handle_InitState();
  this->k = tup2.first;
  this->hs = tup2.second;
  this->io = make_shared<DiskIOHandler>();
}

void Application::crash() {
  LOG("'crashing' and reinitializing");
  LOG("");
  initialize();
}

void Application::Sync() {
  LOG("Sync");

  uint64 id = handle_PushSync(k, hs, io);
  if (id == 0) {
    fail("pushSync failed to allocate id");
  }
  LOG("doing push sync...");

  for (int i = 0; i < 5000; i++) {
    while (this->maybeDoResponse()) { }
    auto tup2 = handle_PopSync(k, hs, io, id);
    bool wait = tup2.first;
    bool success = tup2.second;
    if (success) {
      LOG("doing sync... success!");
      LOG("");
      return;
    } else if (wait) {
      LOG("doing wait...");
      //io.waitForOne();
    } else {
      LOG("doing sync...");
    }
  }
  LOG("giving up");
  fail("Sync operation didn't finish");
}

void Application::Insert(ByteString key, ByteString val)
{
  if (key.size() > (int)MaxKeyLen()) {
    fail("Insert: key is too long");
  }
  if (val.size() > (int)MaxValueLen()) {
    fail("Insert: value is too long");
  }

  for (int i = 0; i < 50; i++) {
    bool success = handle_Insert(k, hs, io, key.as_dafny_seq(), val.as_dafny_seq());
    // TODO remove this to enable more asyncronocity:
    //io.completeWriteTasks();
    this->maybeDoResponse();
    if (success) {
      LOG("doing insert... success!");
      LOG("");
      return;
    } else {
      LOG("doing insert...");
    }
  }
  LOG("giving up");
  fail("operation didn't finish");
}

ByteString Application::Query(ByteString key)
{
  LOG("Query \"" + key.as_string() + "\"");

  if (key.size() > (int)MaxKeyLen()) {
    fail("Query: key is too long");
  }

  for (int i = 0; i < 50; i++) {
    auto result = handle_Query(k, hs, io, key.as_dafny_seq());
    this->maybeDoResponse();
    if (result.first) {
      DafnySequence<byte> val_bytes = result.second;
      LOG("doing query... success!");
      ByteString val(val_bytes);
      LOG("query result is \"" + key.as_string() + "\" -> \"" + val.as_string() + "\"");
      LOG("");
      return val;
    } else {
      LOG("doing query...");
    }
  }
  LOG("giving up");
  fail("operation didn't finish");
}

void Application::QueryAndExpect(ByteString key, ByteString expected_val)
{
  ByteString actual_val = Query(key);
  if (!(expected_val == actual_val)) {
    fail("query returned wrong result");
  }
}

bool Application::maybeDoResponse()
{
  if (io->prepareReadResponse()) {
    handle_ReadResponse(k, hs, io);
    LOG("doing read response...");
    return true;
  }
  else if (io->prepareWriteResponse()) {
    handle_WriteResponse(k, hs, io);
    LOG("doing write response...");
    return true;
  }
  else {
    return false;
  }
}

void Application::Insert(std::string const& key, std::string const& val)
{
  Insert(ByteString(key), ByteString(val));
}

ByteString Application::Query(std::string const& key)
{
  return Query(ByteString(key));
}

void Application::log(std::string const& s) {
  std::cout << s << endl;
}

void Mkfs() {
  DafnyMap<uint64, shared_ptr<vector<byte>>> daf_map = handle_InitDiskBytes();

  unordered_map<uint64, shared_ptr<vector<byte>>> m = daf_map.map;

  if (m.size() == 0) {
    fail("InitDiskBytes failed.");
  }

  /*if (std::filesystem::exists(".veribetrfs-storage")) {
    fail("error: .veribetrfs-storage/ already exists");
  }
  std::filesystem::create_directory(".veribetrfs-storage");*/
  struct stat info;
  if (stat(".veribetrfs-storage", &info) != -1) {
    fail("error: .veribetrfs-storage/ already exists");
  }
  mkdir(".veribetrfs-storage", 0700);

  for (auto p : m) {
    MainDiskIOHandler_Compile::writeSync(p.first, &(*p.second)[0], p.second->size());
  }
}

void ClearIfExists() {
  struct stat info;
  if (stat(".veribetrfs-storage", &info) != -1) {
		// TODO use std::filesystem::remove_all
		system("rm -rf .veribetrfs-storage"); 
  }
}
