#include "BundleWrapper.h"
#include "Application.h"

#include "Bundle.i.h"

//#include <filesystem> // c++17 lol
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <aio.h>
#include <stdio.h>
#include <fcntl.h>

void benchmark_start(string const& name);
void benchmark_end(string const& name);

[[ noreturn ]]
void fail(string err)
{
  cout << "fatal error: " << err << endl;
  exit(1);
}

typedef uint8 byte;

constexpr int MAX_WRITE_REQS_OUT = 8;

namespace MainDiskIOHandler_Compile {
  constexpr int BLOCK_SIZE = 8*1024*1024;

  int nWriteReqsOut = 0;
  int nWriteReqsWaiting = 0;

  struct WriteTask {
    FILE* f;

    vector<byte> bytes;
    aiocb aio_req_write;
    aiocb aio_req_fsync;

    bool made_req;
    bool done;
    
    WriteTask(FILE* f, byte* buf, size_t len) {
      // TODO would be good to eliminate this copy,
      // but the application code might have lingering references
      // to the array.

      // TODO we actually need to fsync the directory too,
      // but it would be even better to just write straight to a device.

      bytes.resize(len);
      std::copy(buf, buf + len, bytes.begin());

      aio_req_write.aio_fildes = fileno(f);
      aio_req_write.aio_offset = 0;
      aio_req_write.aio_buf = &bytes[0];
      aio_req_write.aio_nbytes = len;
      aio_req_write.aio_reqprio = 0;
      aio_req_write.aio_sigevent.sigev_notify = SIGEV_NONE;

      this->f = f;
      this->done = false;
      this->made_req = false;

      nWriteReqsWaiting++;
    }

    void start() {
      int ret = aio_write(&aio_req_write);
      if (ret != 0) {
        cout << "number of writeReqs " << endl;
        if (errno == EAGAIN) { fail("aio_write failed EAGAIN"); }
        else if (errno == EBADF) { fail("aio_write failed EBADF"); }
        else if (errno == EFBIG) { fail("aio_write failed EFBIG"); }
        else if (errno == EINVAL) { fail("aio_write failed EINVAL"); }
        else if (errno == ENOSYS) { fail("aio_write failed ENOSYS"); }
        else { fail("aio_write failed, error unknown, " + to_string(errno)); }
      }

      aio_req_fsync.aio_fildes = fileno(f);
      aio_req_fsync.aio_reqprio = 0;
      aio_req_fsync.aio_sigevent.sigev_notify = SIGEV_NONE;

      ret = aio_fsync(O_SYNC, &aio_req_fsync);
      if (ret != 0) {
        fail("aio_fsync failed");
      }

      this->made_req = true;
      nWriteReqsOut++;
      nWriteReqsWaiting--;
    }

    void wait() {
      if (!this->made_req) {
        fail("wait() failed - request not made yet");
      }
      if (!done) {
        aiocb* aiolist[1];
        aiolist[0] = &aio_req_fsync;
        aio_suspend(aiolist, 1, NULL);

        check_if_complete();
        if (!done) {
          fail("wait failed to complete");
        }
      }
    }

    void check_if_complete() {
      if (!done && made_req) {
        int status = aio_error(&aio_req_fsync);
        if (status == 0) {
          status = aio_error(&aio_req_write);
          if (status != 0) {
            fail("fsync finished but write somehow did not");
          }

          int ret = aio_return(&aio_req_fsync);
          if (ret != 0) {
            fail("fsync returned nonzero");
          }

          ret = aio_return(&aio_req_write);
          if (ret != (int)bytes.size()) {
            fail("fwrite did not write all bytes");
          }

          int close_res = fclose(f);
          if (close_res != 0) {
            fail("read fclose failed");
          }

          done = true;
          nWriteReqsOut--;
        } else if (status != EINPROGRESS) {
          fail("aio_error returned that fsync has failed");
        }
      }
    }
  };

  struct ReadTask {
    DafnySequence<byte> bytes;

    ReadTask(DafnySequence<byte> s) : bytes(s) { }
  };

  string getFilename(uint64 addr) {
    // Convert to hex
    char num[17];
    for (int i = 0; i < 16; i++) {
      int digit = (addr >> (4 * i)) & 0xf;
      num[15 - i] = (digit < 10 ? '0' + digit : 'a' + digit - 10);
    }
    num[16] = '\0';
    return "/tmp/.veribetrfs-storage/" + string(num);
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

  void writeSync(uint64 addr, byte* sector, size_t len) {
    benchmark_start("writeSync");

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

    // TODO according to the fsync documentation, we also need to fsync
    // the directory that the file is in.
    // But really, we should probably be writing straight to a device
    // instead.

    int fsync_res = fsync(fileno(f));
    if (fsync_res != 0) {
      fail("fsync failed");
    }

    int close_res = fclose(f);
    if (close_res != 0) {
      fail("write fclose failed");
    }

    benchmark_end("writeSync");
  }

  void readSync(uint64 addr, uint64 len, byte* sector) {
    benchmark_start("readSync");

    if (addr % BLOCK_SIZE != 0 || len > BLOCK_SIZE) {
      fail("readSync not implemented for these arguments");
    }

    string filename = getFilename(addr);
    int actualRead = readFile(filename, sector, len);
    if ((uint64)actualRead < len) {
      fail("readSync did not find enough bytes");
    }

    benchmark_end("readSync");
  }

  DiskIOHandler::DiskIOHandler() : curId(0) { }

  uint64 DiskIOHandler::write(uint64 addr, DafnyArray<uint8> bytes)
  {
    size_t len = bytes.size();
    if (len > BLOCK_SIZE || addr % BLOCK_SIZE != 0) {
      fail("write not implemented for these arguments");
    }

    FILE* f = fopen(getFilename(addr).c_str(), "w");
    if (f == NULL) {
      fail("write fopen failed");
    }

    //cout << "number of writeReqs: " << writeReqs.size() << endl;

    shared_ptr<WriteTask> writeTask {
      new WriteTask(f, &bytes.at(0), len) };

    if (nWriteReqsOut < MAX_WRITE_REQS_OUT) {
      writeTask->start();
    }

    uint64 id = this->curId;
    this->curId++;

    writeReqs.insert(make_pair(id, writeTask));

    return id;
  }

  uint64 DiskIOHandler::read(uint64 addr, uint64 len)
  {
    DafnySequence<byte> bytes(len);
    readSync(addr, len, bytes.ptr());

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
      this->readResponseBytes = it->second.bytes;
      this->readReqs.erase(it);
      return true;
    } else {
      return false;
    }
  }

  void DiskIOHandler::maybeStartWriteReq() {
    for (auto it = this->writeReqs.begin();
        it != this->writeReqs.end() && nWriteReqsWaiting > 0
          && nWriteReqsOut < MAX_WRITE_REQS_OUT; ++it)
    {
      if (!it->second->made_req) {
        it->second->start();
      }
    }
  }

  bool DiskIOHandler::prepareWriteResponse() {
    for (auto it = this->writeReqs.begin();
        it != this->writeReqs.end(); ++it) {
      shared_ptr<WriteTask> writeTask = it->second;
      writeTask->check_if_complete();
      if (writeTask->done) {
        this->writeResponseId = it->first;
        this->writeReqs.erase(it);
        maybeStartWriteReq();
        return true;
      }
    }
    return false;
  }

  void DiskIOHandler::completeWriteTasks() {
    benchmark_start("completeWriteTasks");
    /*for (auto p : this->writeReqs) {
      if (!p.second->done) {
        p.second->wait();
        maybeStartWriteReq();
      }
    }*/
    while (!this->writeReqs.empty()) {
      waitForOne();
    }
    benchmark_end("completeWriteTasks");
  }
  void DiskIOHandler::waitForOne() {
    vector<aiocb*> tasks;
    tasks.resize(this->writeReqs.size());
    int i = 0;
    for (auto p : this->writeReqs) {
      if (p.second->done) {
        return;
      } else {
        tasks[i] = &p.second->aio_req_fsync;
        i++;
      }
    }
    if (i == 0) {
      fail("waitForOne called with no tasks\n");
    }

    benchmark_start("waitForOne");
    aio_suspend(&tasks[0], i, NULL);
    benchmark_end("waitForOne");

    maybeStartWriteReq();
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

  for (int i = 0; i < 500000; i++) {
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
      io->waitForOne();
    } else {
      LOG("doing sync...");
    }
  }
  LOG("giving up");
  fail("Sync operation didn't finish");
}

void Application::Insert(ByteString key0, ByteString val)
{
  benchmark_start("Application::Insert");

  if (key0.size() > MaxKeyLen()) {
    fail("Insert: key is too long");
  }
  if (val.size() > MaxValueLen()) {
    fail("Insert: value is too long");
  }

  Key key = KeyType_Compile::seq__to__key(key0.as_dafny_seq());

  for (int i = 0; i < 500; i++) {
    benchmark_start("handle_Insert");
    bool success = handle_Insert(k, hs, io, key, val.as_dafny_seq());
    benchmark_end("handle_Insert");
    // TODO remove this to enable more asyncronocity:
    io->completeWriteTasks();

    benchmark_start("Insert-maybeDoResponse");
    this->maybeDoResponse();
    benchmark_end("Insert-maybeDoResponse");

    if (success) {
      LOG("doing insert... success!");
      LOG("");
      benchmark_end("Application::Insert");
      return;
    } else {
      LOG("doing insert...");
    }
  }
  LOG("giving up");
  fail("Insert operation didn't finish");
  benchmark_end("Application::Insert");
}

ByteString Application::Query(ByteString key0)
{
  LOG("Query \"" + key0.as_string() + "\"");

  if (key0.size() > MaxKeyLen()) {
    fail("Query: key is too long");
  }

  Key key = KeyType_Compile::seq__to__key(key0.as_dafny_seq());

  for (int i = 0; i < 5000; i++) {
    auto result = handle_Query(k, hs, io, key);
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
  fail("Query operation didn't finish");
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

UI_Compile::SuccResultList Application::SuccOnce(UI_Compile::RangeStart start, uint64 maxToFind)
{
  LOG("Succ");

  if (maxToFind == 0) {
    fail("SuccOnce should have maxToFind >= 1");
  }

  for (int i = 0; i < 50; i++) {
    auto result = handle_Succ(k, hs, io, start, maxToFind);
    this->maybeDoResponse();
    if (result.first) {
      LOG("doing succ ... success!");
      LOG("");
      return result.second;
    } else {
      LOG("doing succ...");
    }
  }
  LOG("giving up");
  fail("Succ operation didn't finish");
}

vector<pair<ByteString, ByteString>> Application::Succ(ByteString lowerBound, bool inclusive, uint64 targetCount)
{
  if (lowerBound.size() > MaxKeyLen()) {
    fail("Query: key is too long");
  }

  UI_Compile::RangeStart start = inclusive ?
      UI_Compile::RangeStart::create_SInclusive(KeyType_Compile::seq__to__key(lowerBound.as_dafny_seq())) :
      UI_Compile::RangeStart::create_SExclusive(KeyType_Compile::seq__to__key(lowerBound.as_dafny_seq()));
  vector<pair<ByteString, ByteString>> all_results(targetCount);
  uint64 found = 0;
  while (found < targetCount) {
    UI_Compile::SuccResultList srl = SuccOnce(start, targetCount - found);
    for (size_t i = 0; i < srl.results.size(); i++) {
      UI_Compile::SuccResult sr = srl.results.select(i);
      all_results[found] = make_pair(ByteString(KeyType_Compile::key__to__seq(sr.key)), ByteString(sr.value));
      found++;
    }
    if (found == targetCount) {
      break;
    }
    if (srl.end.is_PositiveInf()) {
      all_results.resize(found);
      return all_results;
    }
    if (srl.end.is_EExclusive()) {
      start = UI_Compile::RangeStart::create_SInclusive(srl.end.dtor_key());
    } else {
      start = UI_Compile::RangeStart::create_SExclusive(srl.end.dtor_key());
    }
  }
  return all_results;
}



void Application::log(std::string const& s) {
  std::cout << s << endl;
}

void Mkfs() {
  DafnyMap<uint64, DafnySequence<byte>> daf_map = handle_Mkfs();

  unordered_map<uint64, DafnySequence<byte>> m = daf_map.map;

  if (m.size() == 0) {
    fail("InitDiskBytes failed.");
  }

  /*if (std::filesystem::exists("/tmp/.veribetrfs-storage")) {
    fail("error: /tmp/.veribetrfs-storage/ already exists");
  }
  std::filesystem::create_directory("/tmp/.veribetrfs-storage");*/
  struct stat info;
  if (stat("/tmp/.veribetrfs-storage", &info) != -1) {
    fail("error: /tmp/.veribetrfs-storage/ already exists");
  }
  mkdir("/tmp/.veribetrfs-storage", 0700);

  for (auto p : m) {
    MainDiskIOHandler_Compile::writeSync(
        p.first, p.second.ptr(), p.second.size());
  }
}

void ClearIfExists() {
  struct stat info;
  if (stat("/tmp/.veribetrfs-storage", &info) != -1) {
		// TODO use std::filesystem::remove_all
		int ret = system("rm -rf /tmp/.veribetrfs-storage"); 
		if (ret != 0) {
		  fail("failed to delete /tmp/.veribetrfs-storage");
		}
  }
}
