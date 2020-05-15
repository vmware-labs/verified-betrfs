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
#endif

#include "ioaccounting.h"
#include "stataccounting.h"

#include <strstream>
//#include <filesystem>
#include <chrono>
#include <iostream>
#ifdef VERI_USE_JEMALLOC
#include <jemalloc/jemalloc.h>
#endif // VERI_USE_JEMALLOC

using namespace std;

template< class DB >
inline void performYcsbRead(DB db, ycsbc::CoreWorkload& workload, bool verbose) {
    malloc_accounting_set_scope("performYcsbRead setup");
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

template< class DB >
inline void performYcsbInsert(DB db, ycsbc::CoreWorkload& workload, bool verbose) {
    malloc_accounting_set_scope("performYcsbInsert setup");
    ycsbcwrappers::TxInsert txinsert = ycsbcwrappers::TransactionInsert(workload);
    if (txinsert.values->size() != 1) {
        cerr << db.name << " error: only fieldcount=1 is supported" << endl;
        exit(-1);
    }
    const std::string& value = (*txinsert.values)[0].second;
    if (verbose) {
        cerr << db.name << " [op] INSERT " << txinsert.table << " " << txinsert.key << " " << value << endl;
    }
    malloc_accounting_default_scope();
    // TODO use the table name?
    db.insert(txinsert.key, value);
}

template< class DB >
inline void performYcsbUpdate(DB db, ycsbc::CoreWorkload& workload, bool verbose) {
    malloc_accounting_set_scope("performYcsbUpdate setup");
    ycsbcwrappers::TxUpdate txupdate = ycsbcwrappers::TransactionUpdate(workload);
    if (!workload.write_all_fields()) {
        cerr << db.name << " error: not writing all fields unsupported" << endl;
        exit(-1);
    }
    if (txupdate.values->size() != 1) {
        cerr << db.name << " error: only fieldcount=1 is supported" << endl;
        exit(-1);
    }
    const std::string& value = (*txupdate.values)[0].second;
    if (verbose) {
        cerr << db.name << " [op] UPDATE " << txupdate.table << " " << txupdate.key << " " << value << endl;
    }
    malloc_accounting_default_scope();
    // TODO use the table name?
    db.update(txupdate.key, value);
}

bool cstr_ends_with(const char* haystack, const char* needle) {
  int haystack_len = strlen(haystack);
  int needle_len = strlen(needle);
  if (haystack_len < needle_len) { return false; }
  return strcmp(&haystack[haystack_len - needle_len], needle) == 0;
}

// OS view of heap size
void external_heap_size(size_t* heap, size_t* all_maps) {
  size_t result = -1;
  FILE* fp = fopen("/proc/self/maps", "r");
  size_t total = 0;
  while (true) {
    char space[1000];
    char* line = fgets(space, sizeof(space), fp);
    if (line==NULL) { break; }
    char* remainder;
    size_t base = strtol(line, &remainder, 16);
    size_t end = strtol(&remainder[1], NULL, 16);
    result = end - base;
    total += result;

    if (cstr_ends_with(line, "[heap]\n")) {
      *heap = result;
    }
  }
  fclose(fp);
  *all_maps = total;
}

void proc_io_report() {
  long int read_bytes = -1;
  long int write_bytes = -1;
  FILE* fp = fopen("/proc/self/io", "r");
  while (true) {
    char space[1000];
    char* line = fgets(space, sizeof(space), fp);
    if (line==NULL) { break; }
#define READ_PREFIX "read_bytes"
#define WRITE_PREFIX "write_bytes"
    if (strncmp(line, READ_PREFIX, strlen(READ_PREFIX))==0) {
      read_bytes = strtol(&line[strlen(READ_PREFIX)+2], NULL, 10);
    }
    if (strncmp(line, WRITE_PREFIX, strlen(WRITE_PREFIX))==0) {
      write_bytes = strtol(&line[strlen(WRITE_PREFIX)+2], NULL, 10);
    }
  }
  fclose(fp);
  printf("proc-io read_bytes %ld write_bytes %ld\n", read_bytes, write_bytes);
}

void jemalloc_print_cb(void* opaque, const char* msg) {
  fputs(msg, stdout);
}

void jemalloc_report() {
#ifdef VERI_USE_JEMALLOC
  malloc_stats_print(jemalloc_print_cb, NULL, "j" /*"jmdaxe"*/);
#endif // JEMALLOC_VERSION
}

void cgroups_report() {
  FILE* fp = fopen("/sys/fs/cgroup/memory/VeribetrfsExp/memory.usage_in_bytes", "r");
  char space[1000];
  char* line = fgets(space, sizeof(space), fp);
  fclose(fp);
  printf("cgroups-memory.usage_in_bytes %s", line);

  fp = fopen("/sys/fs/cgroup/memory/VeribetrfsExp/memory.stat", "r");
  while (true) {
    char* line = fgets(space, sizeof(space), fp);
    if (line==NULL) {
      break;
    }
    printf("cgroups-memory.stat %s", line);
  }
  fclose(fp);
}

static int infrequent_clock=0;
template< class DB >
void periodicReport(DB db, const char* phase, int elapsed_ms, int ops_completed) {
    printf("elapsed_ms %d ops %d %s\n", elapsed_ms, ops_completed, phase);

    malloc_accounting_display("periodic");
    db.memDebugFrequent();
    infrequent_clock += 1;
    if (infrequent_clock%3 == 0) {
      db.memDebugInfrequent();
    }

    size_t heap, all_maps;
    external_heap_size(&heap, &all_maps);
    printf("os-map-total %8ld os-map-heap %8ld\n", all_maps, heap);

    IOAccounting::report();
    StatAccounting::report();
    proc_io_report();
    jemalloc_report();
    cgroups_report();
    fflush(stdout);
}

template< class DB >
void ycsbLoad(DB db, ycsbc::CoreWorkload& workload, int num_ops, bool verbose) {
    cerr << db.name << " [step] loading (num ops: " << num_ops << ")" << endl;

    auto clock_start = chrono::steady_clock::now();
    auto clock_last_report = clock_start;
    auto report_interval_ms = 1000;
    for (int i = 0; i < num_ops; ++i) {
        performYcsbInsert(db, workload, verbose);

        auto clock_op_completed = chrono::steady_clock::now();
        if (std::chrono::duration_cast<std::chrono::milliseconds>(
            clock_op_completed - clock_last_report).count() > report_interval_ms) {

            cout << db.name << " (completed " << i << " ops)" << endl;

            int elapsed_ms = std::chrono::duration_cast<std::chrono::milliseconds>(
                clock_op_completed - clock_start).count();
            periodicReport(db, "load", elapsed_ms, i);

            auto report_completed = chrono::steady_clock::now();
            clock_last_report = report_completed;
        }
    }

    cerr << db.name << " [step] sync" << endl;
    db.sync(true);

    auto clock_end = chrono::steady_clock::now();
    long long bench_ns = std::chrono::duration_cast<std::chrono::nanoseconds>(clock_end - clock_start).count();

    double ops_per_sec = ((double) num_ops) / (((double) bench_ns) / 1000000000);

    cerr << db.name << " [step] loading complete" << endl;
    cout << "--\tthroughput(load)\tduration(ns)\toperations\tops/s" << endl;
    cout << db.name << "\tthroughput(load)\t" << bench_ns << "\t" << num_ops << "\t" << ops_per_sec << endl;
}

void print_summary(HDRHistQuantiles& summary, const string db_name, const string op) {
    if (summary.samples() != 0) {
        std::cout << "--" << "\tlatency_ccdf\top\t" << "quantile" << "\t" << "upper_bound(ns)" << std::endl;
        for (
            auto summary_el = summary.next();
            summary_el.has_value();
            summary_el = summary.next()) {

            std::cout << db_name << "\tlatency_ccdf\t" << op << "\t" << summary_el->quantile << "\t" << summary_el->upper_bound << std::endl;
        }
    }
}

bool importantStep(uint64_t i) {
  return false;
  // return (i%10000==0) || (i==59367 || i==59368 || i==74652 || i==74653 || i==90107 || i==90108 || i == 102197 || i == 102198);
}

template< class DB >
void ycsbRun(
    DB db,
    ycsbc::CoreWorkload& workload,
    int num_ops,
    int sync_interval_ops,
    bool verbose) {

    malloc_accounting_set_scope("ycsbRun.setup");
    vector<pair<ycsbc::Operation, string>> operations = {
        make_pair(ycsbc::READ, "read"),
        make_pair(ycsbc::UPDATE, "update"),
        make_pair(ycsbc::INSERT, "insert"),
        make_pair(ycsbc::SCAN, "scan"),
        make_pair(ycsbc::READMODIFYWRITE, "readmodifywrite"),
    };

    map<ycsbc::Operation, unique_ptr<HDRHist>> latency_hist;

    for (auto op : operations) {
        latency_hist[op.first] = move(make_unique<HDRHist>());
    }

    HDRHist sync_latency_hist;
    malloc_accounting_default_scope();

    cerr << db.name << " [step] running experiment (num ops: " << num_ops << ", sync interval " <<
        sync_interval_ops << "ops)" << endl;

    auto clock_start = chrono::steady_clock::now();
    auto clock_prev = clock_start;
    auto clock_last_sync = clock_start;
    int next_sync_ops = sync_interval_ops;
    int display_interval_ms = 10000;
    int next_display_ms = display_interval_ms;
    int have_done_insert_since_last_sync = false;
    int cdf_reset_interval_ops = 100000;
    int next_cdf_reset_ops = cdf_reset_interval_ops;

#define HACK_EVICT_PERIODIC 0
#if HACK_EVICT_PERIODIC
// An experiment that demonstrated that the heap was filling with small
// junk ("heap Kessler syndrome"?): by evicting periodically, we freed
// most of the small junk and kept the heap waste down. TODO okay to clean up.
    int evict_interval_ms = 100000;
    int next_evict_ms = evict_interval_ms;
#endif // HACK_EVICT_PERIODIC

    for (int i = 0; i < num_ops; ++i) {
        auto next_operation = workload.NextOperation();
        switch (next_operation) {
            case ycsbc::READ:
                performYcsbRead(db, workload, verbose);
                break;
            case ycsbc::UPDATE:
                performYcsbUpdate(db, workload, verbose);
                have_done_insert_since_last_sync = true;
                break;
            case ycsbc::INSERT:
                performYcsbInsert(db, workload, verbose);
                have_done_insert_since_last_sync = true;
                break;
            case ycsbc::SCAN:
                cerr << "error: operation SCAN unimplemented" << endl;
                exit(-1);
                break;
            case ycsbc::READMODIFYWRITE:
                cerr << "error: operation READMODIFYWRITE unimplemented" << endl;
                exit(-1);
                break;
            default:
                cerr << "error: invalid NextOperation" << endl;
                exit(-1);
        }

        auto clock_op_completed = chrono::steady_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::nanoseconds>(
            clock_op_completed - clock_prev).count();
        latency_hist[next_operation]->add_value(duration);

        int elapsed_ms = std::chrono::duration_cast<std::chrono::milliseconds>(
            clock_op_completed - clock_start).count();

#if HACK_EVICT_PERIODIC
        if (have_done_insert_since_last_sync && elapsed_ms >= next_evict_ms) {
            printf("evict.");
            db.sync(true);
            have_done_insert_since_last_sync = false;
            db.evictEverything();
            next_evict_ms += evict_interval_ms;
        }
#endif // HACK_EVICT_PERIODIC

        //printf("elapsed_ms %d next_display %d\n", elapsed_ms, next_display_ms);
        if (elapsed_ms >= next_display_ms) {
            periodicReport(db, "run", elapsed_ms, i);
            next_display_ms += display_interval_ms;
        }

        if (i >= next_cdf_reset_ops) {
          IOAccounting::report_histograms();
          IOAccounting::reset_histograms();
          next_cdf_reset_ops += cdf_reset_interval_ops;
        }

        if (have_done_insert_since_last_sync && elapsed_ms >= next_sync_ms) {
            db.sync(false);
            have_done_insert_since_last_sync = false;

            /*
            if (i > 3000000) {
              leakfinder_report(1);
              db.evictEverything();
              leakfinder_report(2);
              exit(0);
            }
            */
            auto sync_completed = chrono::steady_clock::now();
            int sync_time_ms = std::chrono::duration_cast<std::chrono::milliseconds>(
                sync_completed - clock_op_completed).count();

            cout << db.name << " [op] sync (completed " << i << " ops)" << " (sync time " << sync_time_ms << " ms)" << endl;

            #ifdef _YCSB_VERIBETRFS
            #ifdef LOG_QUERY_STATS
            cout << "=========================================" << endl;
            benchmark_dump();
            benchmark_clear();
            cout << "=========================================" << endl;
            #endif
            #endif

            auto sync_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(
                sync_completed - clock_op_completed).count();
            sync_latency_hist.add_value(sync_duration);

            clock_last_sync = sync_completed;
            clock_prev = sync_completed;
            next_sync_ops += sync_interval_ops;

            fflush(stdout);
        } else {
            clock_prev = clock_op_completed;
        }
    }

    auto sync_started = chrono::steady_clock::now();
    db.sync(true);
    have_done_insert_since_last_sync = false;
    auto sync_completed = chrono::steady_clock::now();
    auto sync_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(
        sync_completed - sync_started).count();
    sync_latency_hist.add_value(sync_duration);

    auto clock_end = chrono::steady_clock::now();
    long long bench_ns = std::chrono::duration_cast<std::chrono::nanoseconds>(clock_end - clock_start).count();

    double ops_per_sec = ((double) num_ops) / (((double) bench_ns) / 1000000000);

    cerr << db.name << " [step] experiment complete" << endl;
    cout << "--\tthroughput\tduration(ns)\toperations\tops/s" << endl;
    cout << db.name << "\tthroughput\t" << bench_ns << "\t" << num_ops << "\t" << ops_per_sec << endl;

    malloc_accounting_set_scope("ycsbRun.summary");
    {
        auto sync_summary = sync_latency_hist.summary();
        print_summary(sync_summary, db.name, "sync");

        for (auto op : operations) {
            auto op_summary = latency_hist[op.first]->summary();
            print_summary(op_summary, db.name, op.second);
        }
    }
    malloc_accounting_default_scope();
}

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

    inline void sync(bool fullSync) {
        app.Sync(fullSync);
    }

    inline void evictEverything() {
        app.EvictEverything();
    }

    inline void memDebugFrequent() {
    }

    inline void memDebugInfrequent() {
        app.DebugAccumulator();
        printf("debug-accumulator start\n");
        app.CountAmassAllocations();
        printf("debug-accumulator finish\n");
    }

    inline void cacheDebug() {
      
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
//        woptions.disableWAL = true;
        // this should be the default, but to be careful we don't charge rocks
        // to sync on every write.
        woptions.sync = false;
        rocksdb::Status status = db.Put(woptions, rocksdb::Slice(key), rocksdb::Slice(value));
        assert(status.ok());
    }

    inline void update(const string& key, const string& value) {
        static struct rocksdb::WriteOptions woptions = rocksdb::WriteOptions();
//        woptions.disableWAL = true;
        // this should be the default, but to be careful we don't charge rocks
        // to sync on every write.
        woptions.sync = false;
        rocksdb::Status status = db.Put(woptions, rocksdb::Slice(key), rocksdb::Slice(value));
        assert(status.ok());
    }

    inline void sync(bool /*fullSync*/) {
//        static struct rocksdb::FlushOptions foptions = rocksdb::FlushOptions();
//        rocksdb::Status status = db.Flush(foptions);
        rocksdb::Status status = db.SyncWAL();
        assert(status.ok());
    }

    inline void evictEverything() {
    }

    inline void memDebugFrequent() {}
    inline void memDebugInfrequent() { }

};

const string RocksdbFacade::name = string("rocksdb");
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

    inline void sync(bool /*fullSync*/) {
        asm volatile ("nop");
    }

    inline void evictEverything() {
        asm volatile ("nop");
    }

    inline void memDebugFrequent() {
        asm volatile ("nop");
    }

    inline void memDebugInfrequent() {
        asm volatile ("nop");
    }
};

const string NopFacade::name = string("nop");

template< class DB >
void ycsbLoadAndRun(
    DB db,
    ycsbc::CoreWorkload& workload,
    int record_count,
    int num_ops,
    int sync_interval_ops,
    bool verbose) {

    ycsbLoad(db, workload, record_count, verbose);
    ycsbRun(db, workload, num_ops, sync_interval_ops, verbose);
    malloc_accounting_display("after experiment before teardown");
}

void dump_metadata(const char* workload_filename, const char* base_directory) {
  FILE* fp = fopen("/sys/fs/cgroup/memory/VeribetrfsExp/memory.limit_in_bytes", "r");
  char space[1000];
  char* line = fgets(space, sizeof(space), fp);
  fclose(fp);
  printf("metadata cgroups-memory.limit_in_bytes %s", line);

  printf("metadata workload_filename %s", workload_filename);
  fp = fopen(workload_filename, "r");
  if (fp==NULL) {
    printf("Cannot access workload '%s'!\n", workload_filename);
    exit(-1);
  }
  while (true) {
    char* line = fgets(space, sizeof(space), fp);
    if (line==NULL) {
      break;
    }
    printf("metadata workload %s", line);
  }
  fclose(fp);

  printf("metadata base_directory %s", base_directory);
  fflush(stdout);
  char cmdbuf[1000];
  // yes, this is a security hole. In the measurement framework,
  // not the actual system. You can take the man out of K&R, as they say...
  snprintf(cmdbuf, sizeof(cmdbuf), "df --output=source %s | tail -1", base_directory);
  system(cmdbuf);
  fflush(stdout);
}

int main(int argc, char* argv[]) {
    bool verbose = false;
 
    if (argc < 3) {
        cerr << "error: expects two arguments: the workload spec, and the persistent data directory" << endl;
        exit(-1);
    }

//    leakfinder_mark(1);
//    for (int i=0; i<15; i++) {
//      leakfinder_mark(1);
//    }
//    leakfinder_report(0);

    std::string workload_filename(argv[1]);
    std::string base_directory(argv[2]);
    // (unsupported on macOS 10.14) std::filesystem::create_directory(base_directory);
    // check that base_directory is empty
    int status = std::system(("[ \"$(ls -A " + base_directory + ")\" ]").c_str());

    dump_metadata(workload_filename.c_str(), base_directory.c_str());

    if (status == 0) {
        cerr << "error: " << base_directory << " appears to be non-empty" << endl;
        exit(-1);
    }

    bool do_veribetrkv = false;
    bool do_rocks = false;
    bool do_nop = false;
    for (int i = 3; i < argc; i++) {
      if (string(argv[i]) == "--veribetrkv") {
        do_veribetrkv = true;
      }
      else if (string(argv[i]) == "--rocks") {
        do_rocks = true;
      }
      else if (string(argv[i]) == "--nop") {
        do_nop = true;
      }
      else {
        cerr << "unrecognized: " << argv[i] << endl;
        exit(-1);
      }
    }

    utils::Properties props = ycsbcwrappers::props_from(workload_filename);
    unique_ptr<ycsbc::CoreWorkload> workload(ycsbcwrappers::new_workload(props));
    int record_count = stoi(props[ycsbc::CoreWorkload::RECORD_COUNT_PROPERTY]);

    auto properties_map = props.properties();
    if (properties_map.find("syncintervalops") == properties_map.end()) {
        cerr << "error: spec must provide syncintervalops" << endl;
        exit(-1);
    }
    //int sync_interval_ms = stoi(props["syncintervalms"]);
    int sync_interval_ops = stoi(props["syncintervalops"]);
    int num_ops = stoi(props[ycsbc::CoreWorkload::OPERATION_COUNT_PROPERTY]);


    // == veribetrkv ==
    if (do_veribetrkv) {
    #ifdef _YCSB_VERIBETRFS
        std::string veribetrfs_filename = base_directory + "veribetrfs.img";
        // (unsupported on macOS 10.14) std::filesystem::remove_all(veribetrfs_filename);
        system(("rm -rf " + veribetrfs_filename).c_str());
        Mkfs(veribetrfs_filename);
        Application app(veribetrfs_filename);
        VeribetrkvFacade db(app);
    
        ycsbLoadAndRun(db, *workload, record_count, num_ops, sync_interval_ops, verbose);
    #endif 
    }

    // == rocksdb ==
    if (do_rocks) {
    #ifdef _YCSB_ROCKS
        static string rocksdb_path = base_directory + "rocksdb.db";
        // (unsupported on macOS 10.14) std::filesystem::remove_all(rocksdb_path);
        system(("rm -rf " + rocksdb_path).c_str());

        rocksdb::DB* rocks_db;
        rocksdb::Options options;
        options.create_if_missing = true;
        options.error_if_exists = true;

        // FIXME this is probably not fair, especially when we implement off-thread compaction
        // disables background compaction _and_ flushing
        // https://github.com/facebook/rocksdb/blob/master/include/rocksdb/options.h#L531-L536
        options.max_background_jobs = 0;

        // disabled - we let rocks use the page cache
        // options.use_direct_reads = true;
        // options.use_direct_io_for_flush_and_compaction = true;

        rocksdb::Status status = rocksdb::DB::Open(options, rocksdb_path, &rocks_db);
        assert(status.ok());
        RocksdbFacade db(*rocks_db);

        ycsbLoadAndRun(db, *workload, record_count, num_ops, sync_interval_ops, verbose);
    #endif 
    }


    // == nop ==
    if (do_nop) {
        NopFacade db;

        ycsbLoadAndRun(db, *workload, record_count, num_ops, sync_interval_ops, verbose);
    }
}

