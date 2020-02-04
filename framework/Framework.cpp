#include "BundleWrapper.h"
#include "Application.h"

#include "Bundle.h"

//#include <filesystem> // c++17 lol
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <aio.h>
#include <stdio.h>

[[ noreturn ]]
void fail(string err)
{
  cout << "fatal error: " << err << endl;
  exit(1);
}

typedef uint8 byte;

namespace MainDiskIOHandler_Compile {
  constexpr int BLOCK_SIZE = 8*1024*1024;

  struct WriteTask {
    FILE* f;

    vector<byte> bytes;
    aiocb aio_req_write;
    aiocb aio_req_fsync;

    bool done;
    
    WriteTask(FILE* f, byte* buf, size_t len) {
      // TODO would be good to eliminate this copy,
      // but the application code might have lingering references
      // to the array.

      // TODO we actually need to fsync the directory too,
      // but it would be even better to just write straight to a device.

      bytes.resize(len);
      std::copy(buf, buf + len, bytes.begin());

      this->f = f;
      this->done = false;

      aio_req_write.aio_fildes = fileno(f);
      aio_req_write.aio_offset = 0;
      aio_req_write.aio_buf = &bytes[0];
      aio_req_write.aio_nbytes = len;
      aio_req_write.aio_reqprio = 0;
      aio_req_write.aio_sigevent.sigev_notify = SIGEV_NONE;

      int ret = aio_write(&aio_req_write);
      if (ret != 0) {
        fail("aio_write failed");
      }

      aio_req_fsync.aio_fildes = fileno(f);
      aio_req_fsync.aio_reqprio = 0;
      aio_req_fsync.aio_sigevent.sigev_notify = SIGEV_NONE;

      ret = aio_fsync(O_SYNC, &aio_req_fsync);
      if (ret != 0) {
        fail("aio_fsync failed");
      }
    }

    void wait() {
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
      if (!done) {
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

  void writeSync(uint64 addr, byte* sector, size_t len) {
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

    shared_ptr<WriteTask> writeTask {
      new WriteTask(f, &bytes.at(0), len) };

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

  bool DiskIOHandler::prepareWriteResponse() {
    for (auto it = this->writeReqs.begin();
        it != this->writeReqs.end(); ++it) {
      shared_ptr<WriteTask> writeTask = it->second;
      writeTask->check_if_complete();
      if (writeTask->done) {
        this->writeResponseId = it->first;
        this->writeReqs.erase(it);
        return true;
      }
    }
    return false;
  }

  void DiskIOHandler::completeWriteTasks() {
    for (auto p : this->writeReqs) {
      p.second->wait();
    }
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
    aio_suspend(&tasks[0], i, NULL);
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
      io->waitForOne();
    } else {
      LOG("doing sync...");
    }
  }
  LOG("giving up");
  fail("Sync operation didn't finish");
}

void Application::Insert(ByteString key, ByteString val)
{
  if (key.size() > MaxKeyLen()) {
    fail("Insert: key is too long");
  }
  if (val.size() > MaxValueLen()) {
    fail("Insert: value is too long");
  }

  for (int i = 0; i < 50; i++) {
    bool success = handle_Insert(k, hs, io, key.as_dafny_seq(), val.as_dafny_seq());
    // TODO remove this to enable more asyncronocity:
    io->completeWriteTasks();
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
  fail("Insert operation didn't finish");
}

ByteString Application::Query(ByteString key)
{
  LOG("Query \"" + key.as_string() + "\"");

  if (key.size() > MaxKeyLen()) {
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
      UI_Compile::RangeStart::create_SInclusive(lowerBound.as_dafny_seq()) :
      UI_Compile::RangeStart::create_SExclusive(lowerBound.as_dafny_seq());
  vector<pair<ByteString, ByteString>> all_results(targetCount);
  uint64 found = 0;
  while (found < targetCount) {
    UI_Compile::SuccResultList srl = SuccOnce(start, targetCount - found);
    for (size_t i = 0; i < srl.results.size(); i++) {
      UI_Compile::SuccResult sr = srl.results.select(i);
      all_results[found] = make_pair(ByteString(sr.key), ByteString(sr.value));
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
    MainDiskIOHandler_Compile::writeSync(
        p.first, p.second.ptr(), p.second.size());
  }
}

void ClearIfExists() {
  struct stat info;
  if (stat(".veribetrfs-storage", &info) != -1) {
		// TODO use std::filesystem::remove_all
		int ret = system("rm -rf .veribetrfs-storage"); 
		if (ret != 0) {
		  fail("failed to delete .veribetrfs-storage");
		}
  }
}
