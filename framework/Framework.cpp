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
#include <chrono>

using namespace std;

//#define LOG_QUERY_STATS

//#define USE_DIRECT (1)
#define USE_DIRECT (0)

#ifndef O_NOATIME
#define O_NOATIME (0)
#endif

#define O_DIRECT_FLAG (0)
#if USE_DIRECT
#ifdef O_DIRECT
#undef O_DIRECT_FLAG
#define O_DIRECT_FLAG O_DIRECT
#endif
#endif

[[ noreturn ]]
void fail(std::string err)
{
  std::cout << "fatal error: " << err << std::endl;
  exit(1);
}

constexpr int MAX_WRITE_REQS_OUT = 8;

namespace MainDiskIOHandler_Compile {
#if USE_DIRECT
  uint8_t *aligned_copy(uint8_t* buf, size_t len, size_t *aligned_len) {
    uint8_t *aligned_bytes;
    *aligned_len = (len + 4095) & ~0xfffUL;
    int result = posix_memalign((void **)&aligned_bytes, 4096, *aligned_len);
    if (result) {
      return NULL;
      }
    memcpy(aligned_bytes, buf, len);
    return aligned_bytes;
  }
#else
  uint8_t *aligned_copy(uint8_t* buf, size_t len, size_t *aligned_len) {
    uint8_t *aligned_bytes = (uint8_t *)malloc(len);
    if (aligned_bytes) {
      memcpy(aligned_bytes, buf, len);
      *aligned_len = len;
    }
    return aligned_bytes;
  }
#endif // USE_DIRECT
  
  int nWriteReqsOut = 0;
  int nWriteReqsWaiting = 0;

  struct WriteTask {
    size_t aligned_len;
    uint8_t *aligned_bytes;
    aiocb aio_req_write;

    bool made_req;
    bool done;

    ~WriteTask() {
      free(aligned_bytes);
    }
    
    WriteTask(int fd, uint64 addr, uint8_t* buf, size_t len) {
      // TODO would be good to eliminate this copy,
      // but the application code might have lingering references
      // to the array.

      aligned_bytes = aligned_copy(buf, len, &aligned_len);
      if (aligned_bytes == NULL) {
        fail("Couldn't create aligned copy of buffer");
      }

      aio_req_write.aio_fildes = fd;
      aio_req_write.aio_offset = addr;
      aio_req_write.aio_buf = &aligned_bytes[0];
      aio_req_write.aio_nbytes = aligned_len;
      aio_req_write.aio_reqprio = 0;
      aio_req_write.aio_sigevent.sigev_notify = SIGEV_NONE;

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
        aiolist[0] = &aio_req_write; //&aio_req_fsync;
        aio_suspend(aiolist, 1, NULL);

        check_if_complete();
        if (!done) {
          fail("wait failed to complete");
        }
      }
    }

    void check_if_complete() {
      if (!done && made_req) {
        int status = aio_error(&aio_req_write);
        if (status == 0) {
          ssize_t ret = aio_return(&aio_req_write);
          if (ret < 0 || (size_t)ret != aligned_len) {
            fail("write did not write all bytes");
          }
          done = true;
          nWriteReqsOut--;
        } else if (status != EINPROGRESS) {
          fail("aio_error returned that write has failed");
        }
      }
    }
  };

  struct ReadTask {
    DafnySequence<uint8_t> bytes;

    ReadTask(DafnySequence<uint8_t> s) : bytes(s) { }
  };

  uint64 readFromFile(int fd, uint64 addr, uint8_t* res, int len)
  {
    #ifdef LOG_QUERY_STATS
    auto t1 = chrono::high_resolution_clock::now();
    #endif

    ssize_t count = pread(fd, res, len, addr);

    #ifdef LOG_QUERY_STATS
    auto t2 = chrono::high_resolution_clock::now();
    long long ns = std::chrono::duration_cast<
        std::chrono::nanoseconds>(t2 - t1).count();
    benchmark_append("pread", ns);
    #endif

    if (count < 0) {
      fail("pread failed");
    }
    return (uint64)count;
  }

  void writeSync(int fd, uint64 addr, uint8_t* sector, size_t len) {
    size_t aligned_len;
    uint8_t *aligned_sector;
    aligned_sector = aligned_copy(sector, len, &aligned_len);
    if (aligned_sector == NULL) {
      fail("Couldn't create aligned copy of buffer");
    }    
    
    ssize_t res = pwrite(fd, aligned_sector, aligned_len, addr);

    free(aligned_sector);
    
    if (res < 0 || (uint64)res != aligned_len) {
      perror("write failed");
      printf("fd=%d sector=%p len=%016lx addr=%016lx\n",
             fd, sector, len, (unsigned long)addr);
      fail("pwrite failed");
    }
  }

  void readSync(int fd, uint64 addr, uint64 expected_len, uint64 len_to_read, uint8_t* sector) {
    uint64 actualRead = readFromFile(fd, addr, sector, len_to_read);
    if (actualRead < expected_len) {
      fail("readSync did not find enough bytes");
    }
  }

  DiskIOHandler::DiskIOHandler(string filename) : curId(0) {

    fd = open(filename.c_str(), O_RDWR | O_DIRECT_FLAG | O_DSYNC | O_NOATIME);

    if (fd == -1) {
      fail("open failed");
    }

    #if USE_DIRECT
    #ifdef F_NOCACHE
    int res = fcntl(fd, F_NOCACHE, 1);
    if (res == -1) {
      fail("fcntl F_NOCACHE failed");
    }
    #endif
    #endif
  }

  DiskIOHandler::~DiskIOHandler() {
    if (0 <= fd)
      close(fd);
  }

  uint64 DiskIOHandler::write(uint64 addr, DafnyArray<uint8> bytes)
  {
    size_t len = bytes.size();

    shared_ptr<WriteTask> writeTask {
      new WriteTask(fd, addr, &bytes.at(0), len) };

    if (nWriteReqsOut < MAX_WRITE_REQS_OUT) {
      writeTask->start();
    }

    uint64 id = this->curId;
    this->curId++;

    writeReqs.insert(std::make_pair(id, writeTask));

    return id;
  }

  uint64 DiskIOHandler::read(uint64 addr, uint64 len)
  {
    #ifdef LOG_QUERY_STATS
    benchmark_start("DiskIOHandler::read alloc");
    #endif

    #if USE_DIRECT
    size_t aligned_len = (len + 4095) & ~0xfffULL;
    uint8_t* aligned_res;
    int result = posix_memalign((void **)&aligned_res,
        4096, aligned_len);
    if (result != 0) {
      fail("DiskIOHandler::read couldn't allocate aligned memory");
    }
    DafnySequence<uint8_t> bytes;
    bytes.sptr = std::shared_ptr<uint8_t>(aligned_res, free);
    bytes.start = aligned_res;
    bytes.len = len;
    #else
    DafnySequence<uint8_t> bytes(len);
    uint64 aligned_len = len;
    #endif

    #ifdef LOG_QUERY_STATS
    benchmark_end("DiskIOHandler::read alloc");
    #endif

    readSync(fd, addr, len, aligned_len, bytes.ptr());

    #ifdef LOG_QUERY_STATS
    benchmark_start("DiskIOHandler::read finish");
    #endif

    uint64 id = this->curId;
    this->curId++;

    readReqs.insert(std::make_pair(id, ReadTask(bytes)));

    #ifdef LOG_QUERY_STATS
    benchmark_end("DiskIOHandler::read finish");
    #endif

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
      std::shared_ptr<WriteTask> writeTask = it->second;
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
    while (true) {
      vector<aiocb*> tasks;
      tasks.resize(this->writeReqs.size());
      int i = 0;
      bool any_not_started = false;
      for (auto p : this->writeReqs) {
        p.second->check_if_complete();
        if (p.second->done) {
          continue;
        } else if (p.second->made_req) {
          tasks[i] = &p.second->aio_req_write;
          i++;
        } else {
          any_not_started = true;
        }
      }
      if (i == 0) {
        if (any_not_started) {
          fail("completeWriteTasks: any_not_started");
        }
        break;
      }

      aio_suspend(&tasks[0], i, NULL);

      maybeStartWriteReq();
    }
  }
  void DiskIOHandler::waitForOne() {
    std::vector<aiocb*> tasks;
    tasks.resize(this->writeReqs.size());
    int i = 0;
    for (auto p : this->writeReqs) {
      if (p.second->done) {
        return;
      } else if (p.second->made_req) {
        tasks[i] = &p.second->aio_req_write;
        i++;
      }
    }
    if (i == 0) {
      fail("waitForOne called with no tasks\n");
    }

    aio_suspend(&tasks[0], i, NULL);

    maybeStartWriteReq();
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

void Application::Insert(ByteString key, ByteString val)
{
  #ifdef LOG_QUERY_STATS
  auto t1 = chrono::high_resolution_clock::now();
  #endif

  if (key.size() > MaxKeyLen()) {
    fail("Insert: key is too long");
  }
  if (val.size() > MaxValueLen()) {
    fail("Insert: value is too long");
  }

  for (int i = 0; i < 500000; i++) {
    bool success = handle_Insert(k, hs, io, key.as_dafny_seq(), val.as_dafny_seq());
    // TODO remove this to enable more asyncronocity:
    io->completeWriteTasks();

    this->maybeDoResponse();

    if (success) {
      LOG("doing insert... success!");
      LOG("");

      #ifdef LOG_QUERY_STATS
      auto t2 = chrono::high_resolution_clock::now();

      long long ns = std::chrono::duration_cast<std::chrono::nanoseconds>(t2 - t1).count();
      benchmark_append("Appliation::Insert", ns);
      #endif

      return;
    } else {
      LOG("doing insert...");
    }
  }
  LOG("giving up");
  fail("Insert operation didn't finish");
}

#ifdef LOG_QUERY_STATS
int queryCount = 0;
#endif

ByteString Application::Query(ByteString key)
{
  #ifdef LOG_QUERY_STATS
  auto t1 = chrono::high_resolution_clock::now();
  int num_reads = 0;
  int num_writes = 0;
  #endif

  LOG("Query \"" + key.as_string() + "\"");

  if (key.size() > MaxKeyLen()) {
    fail("Query: key is too long");
  }

  for (int i = 0; i < 500000; i++) {
    auto result = handle_Query(k, hs, io, key.as_dafny_seq());

    #ifdef LOG_QUERY_STATS
    if (io->has_write_task()) {
      num_writes++;
    }
    if (io->has_read_task()) {
      num_reads++;
    }
    #endif

    if (io->has_write_task()) {
      io->completeWriteTasks();
    }
    this->maybeDoResponse();

    if (result.has_value()) {
      DafnySequence<uint8_t> val_bytes = *result;
      LOG("doing query... success!");
      ByteString val(val_bytes);
      LOG("query result is \"" + key.as_string() + "\" -> \"" + val.as_string() + "\"");
      LOG("");

      #ifdef LOG_QUERY_STATS
      if (queryCount > 500) {
        // first few queries would skew results because the cache
        // wouldn't be full yet.
        auto t2 = chrono::high_resolution_clock::now();

        long long ns = std::chrono::duration_cast<std::chrono::nanoseconds>(t2 - t1).count();
        benchmark_append("query-writes-" + to_string(num_writes) +
            "-reads-" + to_string(num_reads), ns);
        benchmark_append("Application::Query", ns);
      }
      queryCount++;
      #endif

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

  for (int i = 0; i < 500000; i++) {
    auto result = handle_Succ(k, hs, io, start, maxToFind);
    this->maybeDoResponse();
    if (result.has_value()) {
      LOG("doing succ ... success!");
      LOG("");
      return *result;
    } else {
      LOG("doing succ...");
    }
  }
  LOG("giving up");
  fail("Succ operation didn't finish");
}

std::vector<std::pair<ByteString, ByteString>> Application::Succ(ByteString lowerBound, bool inclusive, uint64 targetCount)
{
  if (lowerBound.size() > MaxKeyLen()) {
    fail("Query: key is too long");
  }

  UI_Compile::RangeStart start = inclusive ?
      UI_Compile::RangeStart::create_SInclusive(lowerBound.as_dafny_seq()) :
      UI_Compile::RangeStart::create_SExclusive(lowerBound.as_dafny_seq());
  std::vector<std::pair<ByteString, ByteString>> all_results(targetCount);
  uint64 found = 0;
  while (found < targetCount) {
    UI_Compile::SuccResultList srl = SuccOnce(start, targetCount - found);
    for (size_t i = 0; i < srl.results.size(); i++) {
      UI_Compile::SuccResult sr = srl.results.select(i);
      all_results[found] = std::make_pair(ByteString(sr.key), ByteString(sr.value));
      found++;
    }
    if (found == targetCount) {
      break;
    }
    if (srl.end.is_RangeEnd_PositiveInf()) {
      all_results.resize(found);
      return all_results;
    }
    if (srl.end.is_RangeEnd_EExclusive()) {
      start = UI_Compile::RangeStart::create_SInclusive(srl.end.dtor_key());
    } else {
      start = UI_Compile::RangeStart::create_SExclusive(srl.end.dtor_key());
    }
  }
  return all_results;
}



void Application::log(std::string const& s) {
  std::cout << s << std::endl;
}

void Mkfs(string filename) {
  DafnyMap<uint64, DafnySequence<uint8_t>> daf_map = handle_Mkfs();

  std::unordered_map<uint64, DafnySequence<uint8_t>> m = daf_map.map;

  if (m.size() == 0) {
    fail("InitDiskBytes failed.");
  }

  int fd = open(filename.c_str(), O_RDWR | O_DIRECT_FLAG | O_DSYNC | O_NOATIME | O_CREAT, S_IRUSR | S_IWUSR);
  if (fd < 0) {
    fail("Could not open output file: " + filename);
  }
  
  for (auto p : m) {
    MainDiskIOHandler_Compile::writeSync(
        fd, p.first, p.second.ptr(), p.second.size());
  }

  close(fd);
}

