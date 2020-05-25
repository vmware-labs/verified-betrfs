#include <cstdlib>

#ifdef _YCSB_VERIBETRFS
#include "Application.h"
#endif

#include "core_workload.h"
#include "ycsbwrappers.h"
#include "leakfinder.h"
#include "MallocAccounting.h"

#include "hdrhist.hpp"

#ifdef _YCSB_ROCKS
#include "rocksdb/db.h"
#include "rocksdb/table.h"
#include "rocksdb/filter_policy.h"
#endif

#ifdef _YCSB_KYOTO
#include <kchashdb.h>
#endif

#ifdef _YCSB_BERKELEYDB
#include <db_cxx.h>
#include <dbstl_map.h>
#endif

#include <chrono>
#include <iostream>

using namespace std;
using namespace chrono;

template< class C, class D1, class D2 >
void record_duration(HDRHist &hist,
                     const time_point<C,D1> &begin,
                     const time_point<C,D2> &end)
{
  auto duration = duration_cast<nanoseconds>(end - begin);
  hist.add_value(duration.count());
}
  
void print_summary(HDRHistQuantiles& summary, const string workload_name, const string op) {
  if (summary.samples() != 0) {
    cout << "--" << "\tlatency_ccdf\top\t" << "quantile" << "\t" << "upper_bound(ns)" << endl;
    for (auto summary_el = summary.next();
         summary_el.has_value();
         summary_el = summary.next()) {
      
      cout << workload_name << "\tlatency_summary\t" << op << "\t"
           << summary_el->quantile << "\t" << summary_el->upper_bound << endl;
    }
  }
}

void print_ccdf(HDRHistCcdf &ccdf, const string workload_name, const string op) {
  optional<CcdfElement> cur = ccdf.next();
  while (cur.has_value()) {
    cout << workload_name << " latency_ccdf " << op << " "
         << cur->value << " " << cur->fraction << " " << cur->count << endl;
    cur = ccdf.next();
  }
}


static const vector<pair<ycsbc::Operation, string>> YcsbOperations =
  {
   make_pair(ycsbc::READ, "read"),
   make_pair(ycsbc::UPDATE, "update"),
   make_pair(ycsbc::INSERT, "insert"),
   make_pair(ycsbc::SCAN, "scan"),
   make_pair(ycsbc::READMODIFYWRITE, "readmodifywrite"),
  };
  
template< class DB >
class YcsbExecution {
  // Benchmark definition
  DB db;
  string name;
  ycsbc::CoreWorkload& workload;
  bool verbose;
  int record_count;
  int num_ops;
  milliseconds max_sync_interval;
  int max_sync_interval_ops;
  milliseconds progress_report_interval;
  
  // Benchmark results
  map<ycsbc::Operation, unique_ptr<HDRHist>> latency_hist;
  HDRHist load_insert_latency_hist; // for inserts during load phase
  HDRHist sync_latency_hist; // does not include sync at end of load phase
  milliseconds load_duration_ms; // includes time to sync at end
  milliseconds run_duration_ms; // includes time to sync at end

public:
  
  YcsbExecution(DB db,
                string name,
                ycsbc::CoreWorkload& workload,
                int record_count,
                int num_ops,
                bool verbose,
                int max_sync_interval_ms = 0,
                int max_sync_interval_ops = 0,
                int progress_report_interval_ms = 1000)
    : db(db), name(name), workload(workload),
      record_count(record_count), num_ops(num_ops),
      verbose(verbose),
      max_sync_interval(max_sync_interval_ms),
      max_sync_interval_ops(max_sync_interval_ops),
      progress_report_interval(progress_report_interval_ms)
  {
    for (auto op : YcsbOperations) {
      latency_hist[op.first] = move(make_unique<HDRHist>());
    }
  }

  inline void performRead() {
    malloc_accounting_set_scope("performRead setup");
    ycsbcwrappers::TxRead txread = ycsbcwrappers::TransactionRead(workload);
    if (!workload.read_all_fields()) {
      cerr << db.name << " error: not reading all fields unsupported" << endl;
      exit(-1);
    }
    if (verbose) {
      cerr << db.name << " [op] READ " << txread.table << " " << txread.key << " { all fields }" << endl;
    }
    malloc_accounting_default_scope();
    // TODO use the table name?
    db.query(txread.key);
  }

  inline void performInsert(bool load) {
    malloc_accounting_set_scope("performInsert setup");
    ycsbcwrappers::TxInsert txinsert = ycsbcwrappers::TransactionInsert(workload, load);
    if (txinsert.values->size() != 1) {
      cerr << db.name << " error: only fieldcount=1 is supported" << endl;
      exit(-1);
    }
    const string& value = (*txinsert.values)[0].second;
    if (verbose) {
      cerr << db.name << " [op] INSERT " << txinsert.table << " " << txinsert.key << " " << value << endl;
    }
    malloc_accounting_default_scope();
    // TODO use the table name?
    db.insert(txinsert.key, value);
  }

  inline void performUpdate() {
    malloc_accounting_set_scope("performUpdate setup");
    ycsbcwrappers::TxUpdate txupdate = ycsbcwrappers::TransactionUpdate(workload);
    if (!workload.write_all_fields()) {
      cerr << db.name << " error: not writing all fields unsupported" << endl;
      exit(-1);
    }
    if (txupdate.values->size() != 1) {
      cerr << db.name << " error: only fieldcount=1 is supported" << endl;
      exit(-1);
    }
    const string& value = (*txupdate.values)[0].second;
    if (verbose) {
      cerr << db.name << " [op] UPDATE " << txupdate.table << " " << txupdate.key << " " << value << endl;
    }
    malloc_accounting_default_scope();
    // TODO use the table name?
    db.update(txupdate.key, value);
  }

  inline void performReadModifyWrite() {
    malloc_accounting_set_scope("performReadModifyWrite setup");
    ycsbcwrappers::TxUpdate txupdate = ycsbcwrappers::TransactionUpdate(workload);
    if (!workload.write_all_fields()) {
      cerr << db.name << " error: not writing all fields unsupported" << endl;
      exit(-1);
    }
    if (txupdate.values->size() != 1) {
      cerr << db.name << " error: only fieldcount=1 is supported" << endl;
      exit(-1);
    }
    const string& value = (*txupdate.values)[0].second;
    if (verbose) {
      cerr << db.name << " [op] READMODIFYWRITE " << txupdate.table << " " << txupdate.key << " " << value << endl;
    }
    malloc_accounting_default_scope();
    // TODO use the table name?
    db.readmodifywrite(txupdate.key, value);
  }

  inline void performScan() {
    malloc_accounting_set_scope("performScan setup");
    ycsbcwrappers::TxScan txscan = ycsbcwrappers::TransactionScan(workload);
    if (!workload.write_all_fields()) {
      cerr << db.name << " error: not writing all fields unsupported" << endl;
      exit(-1);
    }
    if (verbose) {
      cerr << db.name << " [op] SCAN " << txscan.table << " " << txscan.key << " " << txscan.scan_length << endl;
    }
    malloc_accounting_default_scope();
    // TODO use the table name?
    db.scan(txscan.key, txscan.scan_length);
  }

  void Load() {
    cout << "[step] " << name << " load start (num ops: " << record_count << ")" << endl;

    auto clock_start = steady_clock::now();
    auto clock_next_report = clock_start + progress_report_interval;
    auto clock_op_started = clock_start;
    auto clock_op_completed = clock_start;
    
    for (int i = 0; i < record_count; ++i) {
      clock_op_started = steady_clock::now();
        performInsert(true /* load */);
      clock_op_completed = steady_clock::now();
      record_duration(load_insert_latency_hist, clock_op_started, clock_op_completed);

      if (clock_next_report < clock_op_completed) {
        auto duration_ms = duration_cast<milliseconds>(
                        clock_op_completed - clock_start).count();
        cout << "[step] " << name << " load progress " << duration_ms << " ms " << i << " ops" << endl;
        malloc_accounting_status();
        clock_next_report = clock_op_completed + progress_report_interval;
      }
    }

    auto duration_ms = duration_cast<milliseconds>(clock_op_completed - clock_start);
    cout << "[step] " << name << " load sync " << duration_ms.count() << " ms" << endl;
    db.sync(true);

    auto clock_end = steady_clock::now();
    load_duration_ms = duration_cast<milliseconds>(clock_end - clock_start);
    cout << "[step] " << name << " load end " << load_duration_ms.count() << " ms" << endl;

    auto load_duration_ns = duration_cast<nanoseconds>(clock_end - clock_start);
    assert(load_duration_ns.count() != 0);

    double load_duration_s = duration_cast<nanoseconds>(clock_end - clock_start).count() / 1000000000.0;
    double throughput = record_count / load_duration_s;
    cout << "[step] " << name << " load throughput " << throughput << " ops/sec" << endl;

    auto load_insert_summary = load_insert_latency_hist.summary();
    auto load_insert_ccdf = load_insert_latency_hist.ccdf();
    print_summary(load_insert_summary, name, "load");
    print_ccdf(load_insert_ccdf, name, "load");
  }

  void Run() {
    malloc_accounting_set_scope("ycsbRun.setup");
    malloc_accounting_default_scope();

    auto clock_start  = steady_clock::now();
    auto next_sync    = clock_start + max_sync_interval;
    auto next_display = clock_start + progress_report_interval;

    int next_sync_ops = 0 < max_sync_interval_ops ? max_sync_interval_ops : num_ops+1;
    bool have_done_insert_since_last_sync = false;
    
#define HACK_EVICT_PERIODIC 0
#if HACK_EVICT_PERIODIC
    // An experiment that demonstrated that the heap was filling with small
    // junk ("heap Kessler syndrome"?): by evicting periodically, we freed
    // most of the small junk and kept the heap waste down. TODO okay to clean up.
    int evict_interval_ms = 100000;
    int next_evict_ms = evict_interval_ms;
#endif // HACK_EVICT_PERIODIC

#define HACK_PROBE_PERIODIC 1
#if HACK_PROBE_PERIODIC
    // An experiment to periodically study how the kv allocations are distributed
    int probe_interval_ms = 50000;
    int next_probe_ms = probe_interval_ms;
#endif // HACK_PROBE_PERIODIC

    cout << "[step] " << name << " run start (num ops: " << num_ops << ", sync interval " <<
      max_sync_interval.count() << " ms, sync ops " << max_sync_interval_ops << ")" << endl;

    for (int i = 0; i < num_ops; ++i) {
      auto next_operation = workload.NextOperation();
      auto clock_op_started = steady_clock::now();
      switch (next_operation) {
      case ycsbc::READ:
        performRead();
        break;
      case ycsbc::UPDATE:
        performUpdate();
        have_done_insert_since_last_sync = true;
        break;
      case ycsbc::INSERT:
        performInsert(false /* not load */);
        have_done_insert_since_last_sync = true;
        break;
      case ycsbc::SCAN:
        performScan();
        break;
      case ycsbc::READMODIFYWRITE:
        performReadModifyWrite();
        have_done_insert_since_last_sync = true;
        break;
      default:
        cerr << "error: invalid NextOperation" << endl;
        exit(-1);
      }
      auto clock_op_completed = steady_clock::now();
      record_duration(*latency_hist[next_operation], clock_op_started, clock_op_completed);

      if (next_display <= clock_op_completed) {
        malloc_accounting_display("periodic");
        auto elapsed_ms = duration_cast<milliseconds>(clock_op_completed - clock_start);
        cout << "[step] " << name << " run progress " << elapsed_ms.count() << " ms " <<  i << " ops" << endl;
        next_display += progress_report_interval;
      }

      if (have_done_insert_since_last_sync &&
          ((0 < max_sync_interval.count() && next_sync < clock_op_completed)
           || next_sync_ops <= i)) {
        auto sync_started = steady_clock::now();
        milliseconds elapsed_ms = duration_cast<milliseconds>(sync_started - clock_start);
        cout << "[step] " << name << " run sync start " << elapsed_ms.count() << " ms " << i << " ops" << endl;
        db.sync(false);
        auto sync_completed = steady_clock::now();
        elapsed_ms = duration_cast<milliseconds>(sync_completed - clock_start);
        cout << "[step] " << name << " run sync end " << elapsed_ms.count() << " ms " << i << " ops" << endl;
        record_duration(sync_latency_hist, sync_started, sync_completed);
        have_done_insert_since_last_sync = false;
        next_sync = sync_completed + max_sync_interval;
        next_sync_ops = i + max_sync_interval_ops;
        
        malloc_accounting_status();
#ifdef _YCSB_VERIBETRFS
#ifdef LOG_QUERY_STATS
        cout << "=========================================" << endl;
        benchmark_dump();
        benchmark_clear();
        cout << "=========================================" << endl;
#endif
#endif
        fflush(stdout);
      }
    }

    if (have_done_insert_since_last_sync) {
      auto sync_started = steady_clock::now();
      milliseconds elapsed_ms = duration_cast<milliseconds>(sync_started - clock_start);
      cout << "[step] " << name << " sync start " << elapsed_ms.count()  << " ms " << num_ops << " ops" << endl;
      db.sync(true);
      auto sync_completed = steady_clock::now();
      elapsed_ms = duration_cast<milliseconds>(sync_completed - clock_start);
      cout << "[step] " << name << " sync end " << elapsed_ms.count() << " ms " << num_ops << " ops" << endl;
      record_duration(sync_latency_hist, sync_started, sync_completed);
      have_done_insert_since_last_sync = false;
      next_sync = sync_completed + max_sync_interval;
      next_sync_ops = num_ops + max_sync_interval_ops;
    }

    auto clock_end = steady_clock::now();
    run_duration_ms = duration_cast<milliseconds>(clock_end - clock_start);

    double run_duration_s = duration_cast<nanoseconds>(clock_end - clock_start).count() / 1000000000.0;
    double throughput = num_ops / run_duration_s;
    cout << "[step] " << name << " run throughput " << throughput << " ops/sec" << endl;
    
    malloc_accounting_set_scope("ycsbRun.summary");
    {
      for (auto op : YcsbOperations) {
        auto op_summary = latency_hist[op.first]->summary();
        auto op_ccdf = latency_hist[op.first]->ccdf();
        print_summary(op_summary, name, op.second);
        print_ccdf(op_ccdf, name, op.second);
      }
      auto sync_summary = sync_latency_hist.summary();
      auto sync_ccdf = sync_latency_hist.ccdf();
      print_summary(sync_summary, name, "sync");
      print_ccdf(sync_ccdf, name, "sync");
    }
    malloc_accounting_default_scope();
  }

  void LoadAndRun() {
    Load();
    Run();
    malloc_accounting_display("after experiment before teardown");
  }
};

#ifdef _YCSB_VERIBETRFS
class VeribetrkvFacade {
protected:
    Application& app;

public:
    static const string name;

    VeribetrkvFacade(Application& app) : app(app) { }

    inline void query(const string& key) {
        app.Query(key);
    }

    inline void insert(const string& key, const string& value) {
        app.Insert(key, value);
    }

    inline void update(const string& key, const string& value) {
        app.Insert(key, value);
    }

    inline void readmodifywrite(const string& key, const string& value) {
      update(key, value);
    }

    inline void scan(const string &key, int len) {
      app.Succ(ByteString(key), true, len);
    }
  
    inline void sync(bool fullSync) {
        app.Sync(fullSync);
    }

    inline void evictEverything() {
        app.EvictEverything();
    }

    inline void CountAmassAllocations() {
        app.CountAmassAllocations();
        printf("debug-accumulator finish\n");
    }

    inline void cacheDebug() {
      //app.CacheDebug();
    }
};

const string VeribetrkvFacade::name = string("veribetrkv");
#endif

#ifdef _YCSB_ROCKS
class RocksdbFacade {
protected:
    rocksdb::DB& db;
    
public:
    static const string name;

    RocksdbFacade(rocksdb::DB& db) : db(db) { }

    inline void query(const string& key) {
        static struct rocksdb::ReadOptions roptions = rocksdb::ReadOptions();
        string value;
        rocksdb::Status status = db.Get(roptions, rocksdb::Slice(key), &value);
        assert(status.ok() || status.IsNotFound()); // TODO is it expected we're querying non-existing keys?
    }

    inline void insert(const string& key, const string& value) {
        static struct rocksdb::WriteOptions woptions = rocksdb::WriteOptions();
        woptions.disableWAL = true;
        rocksdb::Status status = db.Put(woptions, rocksdb::Slice(key), rocksdb::Slice(value));
        assert(status.ok());
    }

    inline void update(const string& key, const string& value) {
        static struct rocksdb::WriteOptions woptions = rocksdb::WriteOptions();
        woptions.disableWAL = true;
        rocksdb::Status status = db.Put(woptions, rocksdb::Slice(key), rocksdb::Slice(value));
        assert(status.ok());
    }

    inline void readmodifywrite(const string& key, const string& value) {
      update(key, value);
    }
  
    inline void scan(const string &key, int len) {
      rocksdb::Iterator* it = db.NewIterator(rocksdb::ReadOptions());
      int i = 0;
      for (it->Seek(key); i < len && it->Valid(); it->Next()) {
        i++;
      }
      delete it;
    }
  
    inline void sync(bool /*fullSync*/) {
        static struct rocksdb::FlushOptions foptions = rocksdb::FlushOptions();
        rocksdb::Status status = db.Flush(foptions);
        assert(status.ok());
    }

    inline void evictEverything() {
    }

    inline void CountAmassAllocations() {
    }
};

const string RocksdbFacade::name = string("rocksdb");
#endif

#ifdef _YCSB_KYOTO
class KyotoFacade {
protected:
    kyotocabinet::TreeDB &db;
    
public:
    static const string name;

    KyotoFacade(kyotocabinet::TreeDB &db) : db(db) { }

    inline void query(const string& key) {
      string result;
      db.get(key, &result);
    }

    inline void insert(const string& key, const string& value) {
      if (!db.set(key, value)) {
        cout << "Insert failed" << endl;
        abort();
      }
    }

    inline void update(const string& key, const string& value) {
      if (!db.set(key, value)) {
        cout << "Update failed" << endl;
        abort();
      }
    }

    inline void readmodifywrite(const string& key, const string& value) {
      query(key);
      update(key, value);
    }

    inline void scan(const string &key, int len) {
      kyotocabinet::DB::Cursor *cursor = db.cursor();
      assert(cursor);
      assert(cursor->jump(key));
      int i = 0;
      while (i < len && cursor->step())
        i++;
      delete cursor;
    }
  
    inline void sync(bool /*fullSync*/) {
      db.synchronize();
    }

    inline void evictEverything() {
    }

    inline void CountAmassAllocations() {
    }
};

const string KyotoFacade::name = string("kyotodb");
#endif

#ifdef _YCSB_BERKELEYDB
class BerkeleyDBFacade {
protected:
  //DbEnv *env;
    Db* pdb;
    dbstl::db_map<string, string> *huge_map;

public:
    static const string name;

  BerkeleyDBFacade(Db *_pdb) : pdb(_pdb) {
    huge_map = new dbstl::db_map<string, string>(pdb, NULL);
  }

    inline void query(const string& key) {
      string result;
      try {
        const auto &t = *huge_map; // Get a const reference so operator[] doesn't insert key if it doesn't exist.
        result = t[key];
      } catch (DbException& e) {
        cerr << "DbException: " << e.what() << endl;
        abort();
      } catch (std::exception& e) {
        cerr << e.what() << endl;
        abort();
      }
    }

    inline void insert(const string& key, const string& value) {
      try {
        (*huge_map)[key] = value;
      } catch (DbException& e) {
        cerr << "DbException: " << e.what() << endl;
        abort();
      } catch (std::exception& e) {
        cerr << e.what() << endl;
        abort();
      }
    }

    inline void update(const string& key, const string& value) {
      insert(key, value);
    }

    inline void readmodifywrite(const string& key, const string& value) {
      query(key);
      update(key, value);
    }
  
    inline void scan(const string &key, int len) {
      int i = 0;
      auto iter = huge_map->begin(); // lower_bound() seems to be broken in berkeleydb
      while(i < len && iter != huge_map->end()) {
        ++iter;
        i++;
      }
    }
  
    inline void sync(bool /*fullSync*/) {
      pdb->sync(0);
    }

    inline void evictEverything() {
    }

    inline void CountAmassAllocations() {
    }
};

const string BerkeleyDBFacade::name = string("berkeleydb");
#endif

class NopFacade {
public:
    static const string name;

    NopFacade() { }

    inline void query(const string& key) {
        asm volatile ("nop");
    }

    inline void insert(const string& key, const string& value) {
        asm volatile ("nop");
    }

    inline void update(const string& key, const string& value) {
        asm volatile ("nop");
    }

    inline void readmodifywrite(const string& key, const string& value) {
    }

    inline void scan(const string &key, int len) {
    }
  
    inline void sync(bool /*fullSync*/) {
        asm volatile ("nop");
    }

    inline void evictEverything() {
        asm volatile ("nop");
    }

    inline void CountAmassAllocations() {
        asm volatile ("nop");
    }
    inline void cacheDebug() {
        asm volatile ("nop");
    }
};

const string NopFacade::name = string("nop");

void dump_metadata(const char* workload_filename, const char* database_filename) {
  FILE* fp;
  char space[1000];
  char* line;

  // This could output wrong info if we are not actually running in
  // the cgroup.
  //
  // fp = fopen("/sys/fs/cgroup/memory/VeribetrfsExp/memory.limit_in_bytes", "r");
  // if (fp) {
  //   line = fgets(space, sizeof(space), fp);
  //   fclose(fp);
  //   printf("metadata cgroups-memory.limit_in_bytes %s", line);
  // }

  printf("metadata workload_filename %s", workload_filename);
  fp = fopen(workload_filename, "r");
  while (true) {
    char* line = fgets(space, sizeof(space), fp);
    if (line==NULL) {
      break;
    }
    printf("metadata workload %s", line);
  }
  fclose(fp);

  printf("metadata database_filename %s", database_filename);
  fflush(stdout);
  char cmdbuf[1000];
  // yes, this is a security hole. In the measurement framework,
  // not the actual system. You can take the man out of K&R, as they say...
  snprintf(cmdbuf, sizeof(cmdbuf), "df --output=source %s | tail -1", database_filename);
  system(cmdbuf);
  fflush(stdout);
}

template< class DbFacade >
void runOneWorkload(DbFacade db, string workload_filename, string database_filename,
                    ycsbc::CoreWorkload &workload,
                    bool load, bool do_nop, bool verbose)
{
  utils::Properties props = ycsbcwrappers::props_from(workload_filename);
  auto properties_map = props.properties();
  workload.Init(props, !load);

  int record_count = stoi(props[ycsbc::CoreWorkload::RECORD_COUNT_PROPERTY]);
  int num_ops = stoi(props[ycsbc::CoreWorkload::OPERATION_COUNT_PROPERTY]);

  int sync_interval_ms =  0;
  int sync_interval_ops = 0;

  string workload_name;
  
  if (properties_map.find("syncintervalms") != properties_map.end()) {
    sync_interval_ms= stoi(props["syncintervalms"]);
  }
  
  if (properties_map.find("syncintervalops") != properties_map.end()) {
    sync_interval_ops = stoi(props["syncintervalops"]);
  }
  
  if (properties_map.find("workloadname") != properties_map.end()) {
    workload_name = props["workloadname"];
  } else {
    workload_name = workload_filename;
  }
  
  dump_metadata(workload_filename.c_str(), database_filename.c_str());

  if (do_nop) {
    NopFacade nopdb;
    YcsbExecution ycsbExecution(nopdb, workload_name, workload, record_count, num_ops, verbose,
                                sync_interval_ms, sync_interval_ops);
    if (load)
      ycsbExecution.Load();
    else
      ycsbExecution.Run();
  } else {
    YcsbExecution ycsbExecution(db, workload_name, workload, record_count, num_ops, verbose,
                                sync_interval_ms, sync_interval_ops);
    if (load)
      ycsbExecution.Load();
    else
      ycsbExecution.Run();
  }
}

void pretendToDoLoadPhase(const string &workload_filename, ycsbc::CoreWorkload &workload)
{
  utils::Properties props = ycsbcwrappers::props_from(workload_filename);
  auto properties_map = props.properties();
  workload.Init(props, false);
  workload.AdvanceToEndOfLoad();
}

void usage(int argc, char **argv)
{
  cerr << "Usage: " << argv[0] << " ";
#ifdef _YCSB_VERIBETRFS
  cout << "<veribetrkv.img> ";
#endif
#ifdef _YCSB_ROCKS
  cout << "<rocksdb-directory> ";
#endif
#ifdef _YCSB_BERKELEYDB
  cout << "<berkeley.db> ";
#endif
#ifdef _YCSB_KYOTO
  cout << "<kyoto.cbt> ";
#endif
  cout << "[--nop] [--verbose] [--preloaded] ";
#ifdef _YCSB_ROCKS
  cout << "[--filters] ";
#endif
  cout << "<load-workload.spec> [run-workload1.spec...]" << endl;
  cout << "  --nop: use a no-op database" << endl;
  cout << "  --preloaded: don't format database.  Database must have been loaded " << endl;
  cout << "               with the given load workload." << endl;
#ifdef _YCSB_ROCKS
  cout << "  --filters: enable filters" << endl;
#endif
  exit(-1);
}  

int main(int argc, char* argv[]) {
  if (argc < 3)
    usage(argc, argv);
  
  bool do_nop = false;
  bool verbose = false;
  bool preloaded = false;
#ifdef _YCSB_ROCKS
  bool use_filters = false;
#endif
  std::string database_filename(argv[1]);

  int first_workload_filename;
  int i;
  for (i = 2; i < argc; i++) {
    if (string(argv[i]) == "--nop") {
      do_nop = true;
    } else if (string(argv[i]) == "--verbose") {
      verbose = true;
    } else if (string(argv[i]) == "--preloaded") {
      preloaded = true;
#ifdef _YCSB_ROCKS
    } else if (string(argv[i]) == "--filters") {
      use_filters = true;
#endif
    } else {
      break;
    }
  }
  first_workload_filename = i;
  
  // == veribetrkv ==
#ifdef _YCSB_VERIBETRFS
  if (!preloaded)
    Mkfs(database_filename);
  Application app(database_filename);
  VeribetrkvFacade db(app);
#endif

  // == rocksdb ==
#ifdef _YCSB_ROCKS
  rocksdb::DB* rocks_db;
  rocksdb::Options options;
  if (!preloaded)
    options.create_if_missing = true;
  //options.error_if_exists = true;
    
  // FIXME this is probably not fair, especially when we implement off-thread compaction
  // disables background compaction _and_ flushing
  // https://github.com/facebook/rocksdb/blob/master/include/rocksdb/options.h#L531-L536
  options.max_background_jobs = 0;
    
  // disabled - we let rocks use the page cache
  // options.use_direct_reads = true;
  // options.use_direct_io_for_flush_and_compaction = true;

  if (use_filters) {
    rocksdb::BlockBasedTableOptions table_options;
    table_options.filter_policy.reset(rocksdb::NewBloomFilterPolicy(10, false));
    options.table_factory.reset(rocksdb::NewBlockBasedTableFactory(table_options));
  }
  
  rocksdb::Status status = rocksdb::DB::Open(options, database_filename, &rocks_db);
  assert(status.ok());
  RocksdbFacade db(*rocks_db);
#endif

  // == kyotodb ==
#ifdef _YCSB_KYOTO
  kyotocabinet::TreeDB tdb;
  bool success = tdb.open(database_filename,
                          kyotocabinet::TreeDB::OWRITER
                          | (preloaded ? 0 : kyotocabinet::TreeDB::OCREATE)
                          | kyotocabinet::TreeDB::ONOLOCK);
  if (!success)
    abort();
  KyotoFacade db(tdb);
#endif 

  // == berkeleydb ==
#ifdef _YCSB_BERKELEYDB
  Db* pdb;
  pdb = new Db(NULL, DB_CXX_NO_EXCEPTIONS);
  assert(pdb);
  if (pdb->open(NULL, database_filename.c_str(), NULL, DB_BTREE, preloaded ? 0 : DB_CREATE, 0)) {
    cerr << "Failed to open database " << database_filename << endl;
    abort();
  }
  BerkeleyDBFacade db(pdb);
#endif

  ycsbc::CoreWorkload workload_template;
  for (i = first_workload_filename; i < argc; i++) {
    if (preloaded && i == first_workload_filename)
      pretendToDoLoadPhase(argv[i], workload_template);
    else
      runOneWorkload(db, argv[i], database_filename, workload_template,
                     i == first_workload_filename, do_nop, verbose);
  }
  
#ifdef _YCSB_VERIBETRFS
  // No shutdown needed
#endif
  
#ifdef _YCSB_ROCKS
  // No shutdown needed
#endif
  
#ifdef _YCSB_KYOTO
  if (!tdb.close()) {
    cout << "Failed to close " << database_filename;
    abort();
  }
#endif

#ifdef _YCSB_BERKELEYDB
  if (pdb != NULL) {
    if (pdb->close(0)) {
      cerr << "Failed to close database" << endl;
      abort();
    }
    delete pdb;
  }
#endif

  return 0;
}

