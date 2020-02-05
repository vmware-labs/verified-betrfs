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

[[ noreturn ]]
void fail(string err)
{
  cout << "fatal error: " << err << endl;
  exit(1);
}

typedef uint8 byte;

namespace MainDiskIOHandler_Compile {
  constexpr int BLOCK_SIZE = 8*1024*1024;

  byte *aligned_copy(byte* buf, size_t len, size_t *aligned_len) {
    byte *aligned_bytes;
    *aligned_len = (len + 4095) & ~0xfffUL;
    int result = posix_memalign((void **)&aligned_bytes, 4096, *aligned_len);
    if (result) {
      return NULL;
    }
    memcpy(aligned_bytes, buf, len);
    return aligned_bytes;
  }
  
  struct WriteTask {
    size_t aligned_len;
    byte *aligned_bytes;
    aiocb aio_req_write;

    bool done;

    ~WriteTask() {
      free(aligned_bytes);
    }
    
    WriteTask(int fd, uint64 addr, byte* buf, size_t len) {
      // TODO would be good to eliminate this copy,
      // but the application code might have lingering references
      // to the array.

      aligned_bytes = aligned_copy(buf, len, &aligned_len);
      if (aligned_bytes == NULL) {
        fail("Couldn't create aligned copy of buffer");
      }
      
      this->done = false;

      aio_req_write.aio_fildes = fd;
      aio_req_write.aio_offset = addr;
      aio_req_write.aio_buf = &aligned_bytes[0];
      aio_req_write.aio_nbytes = aligned_len;
      aio_req_write.aio_reqprio = 0;
      aio_req_write.aio_sigevent.sigev_notify = SIGEV_NONE;

      int ret = aio_write(&aio_req_write);
      if (ret != 0) {
        fail("aio_write failed");
      }
    }

    void wait() {
      if (!done) {
        aiocb* aiolist[1];
        aiolist[0] = &aio_req_write; //&aio_req_fsync;
        aio_suspend(aiolist, 1, NULL);

        check_if_complete();
        if (!done) {
          fail("wait failed to complete");
        }
      }
    }

    void check_if_complete() {
      if (!done) {
        int status = aio_error(&aio_req_write);
        if (status == 0) {
          ssize_t ret = aio_return(&aio_req_write);
          if (ret < 0 || (size_t)ret != aligned_len) {
            fail("write did not write all bytes");
          }
          done = true;
        } else if (status != EINPROGRESS) {
          fail("aio_error returned that write has failed");
        }
      }
    }
  };

  struct ReadTask {
    DafnySequence<byte> bytes;

    ReadTask(DafnySequence<byte> s) : bytes(s) { }
  };

  uint64 readFromFile(int fd, uint64 addr, byte* res, int len)
  {
    size_t aligned_len = (len + 4095) & ~0xfffULL;
    byte *aligned_res;
    int result = posix_memalign((void **)&aligned_res, 4096, aligned_len);
    if (result != 0) {
      fail("Couldn't allocate aligned memory");
    }
    
    ssize_t count = pread(fd, aligned_res, aligned_len, addr);
    if (count < 0) {
      free(aligned_res);
      fail("pread failed");
    }
    memcpy(res, aligned_res, len);
    free(aligned_res);
    
    return (uint64)count;
  }

  void writeSync(int fd, uint64 addr, byte* sector, size_t len) {
    if (len > BLOCK_SIZE || addr % BLOCK_SIZE != 0) {
      fail("writeSync not implemented for these arguments");
    }

    size_t aligned_len;
    byte *aligned_sector;
    aligned_sector = aligned_copy(sector, len, &aligned_len);
    if (aligned_sector == NULL) {
      fail("Couldn't create aligned copy of buffer");
    }    
    
    ssize_t res = pwrite(fd, aligned_sector, aligned_len, addr);

    free(aligned_sector);
    
    if (res < 0 || (uint64)res != aligned_len) {
      perror("write failed");
      printf("fd=%d sector=%p len=%016lx addr=%016lx\n",
             fd, sector, len, addr);
      fail("pwrite failed");
    }
  }

  void readSync(int fd, uint64 addr, uint64 len, byte* sector) {
    if (addr % BLOCK_SIZE != 0 || len > BLOCK_SIZE) {
      fail("readSync not implemented for these arguments");
    }

    uint64 actualRead = readFromFile(fd, addr, sector, len);
    if (actualRead < len) {
      fail("readSync did not find enough bytes");
    }
  }

  DiskIOHandler::DiskIOHandler(string filename) : curId(0) {
    // Should probably throw an error if this fails
    fd = open(filename.c_str(), O_RDWR | O_DIRECT | O_DSYNC | O_NOATIME);
  }

  uint64 DiskIOHandler::write(uint64 addr, DafnyArray<uint8> bytes)
  {
    size_t len = bytes.size();
    if (len > BLOCK_SIZE || addr % BLOCK_SIZE != 0) {
      fail("write not implemented for these arguments");
    }

    shared_ptr<WriteTask> writeTask {
      new WriteTask(fd, addr, &bytes.at(0), len) };

    uint64 id = this->curId;
    this->curId++;

    writeReqs.insert(make_pair(id, writeTask));

    return id;
  }

  uint64 DiskIOHandler::read(uint64 addr, uint64 len)
  {
    DafnySequence<byte> bytes(len);
    readSync(fd, addr, len, bytes.ptr());

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
        tasks[i] = &p.second->aio_req_write;
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

Application::Application(string filename) {
  this->filename = filename;
  initialize();
}

void Application::initialize() {
  auto tup2 = handle_InitState();
  this->k = tup2.first;
  this->hs = tup2.second;
  this->io = make_shared<DiskIOHandler>(this->filename);
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

  for (int i = 0; i < 500; i++) {
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

  for (int i = 0; i < 5000; i++) {
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

void Mkfs(string filename) {
  DafnyMap<uint64, DafnySequence<byte>> daf_map = handle_Mkfs();

  unordered_map<uint64, DafnySequence<byte>> m = daf_map.map;

  if (m.size() == 0) {
    fail("InitDiskBytes failed.");
  }

  int fd = open(filename.c_str(), O_RDWR | O_DIRECT | O_DSYNC | O_NOATIME | O_CREAT, S_IRUSR | S_IWUSR);
  if (fd < 0) {
    fail("Could not open output file: " + filename);
  }
  
  for (auto p : m) {
    MainDiskIOHandler_Compile::writeSync(
        fd, p.first, p.second.ptr(), p.second.size());
  }
}

