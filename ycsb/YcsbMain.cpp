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

#ifdef _YCSB_KYOTO
#include <kchashdb.h>
#endif

#ifdef _YCSB_BERKELEYDB
#include <db_cxx.h>
#include <dbstl_map.h>
#endif

#include <strstream>
//#include <filesystem>
#include <chrono>
#include <iostream>

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
            malloc_accounting_status();
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

template< class DB >
void ycsbRun(
    DB db,
    ycsbc::CoreWorkload& workload,
    int num_ops,
    int sync_interval_ms,
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
        sync_interval_ms << "ms)" << endl;

    auto clock_start = chrono::steady_clock::now();
    auto clock_prev = clock_start;
    auto clock_last_sync = clock_start;
    int next_sync_ms = sync_interval_ms;
    int display_interval_ms = 10000;
    int next_display_ms = display_interval_ms;
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
#if HACK_PROBE_PERIODIC
        if (elapsed_ms >= next_probe_ms) {
            printf("probe.");
            db.CountAmassAllocations();
            next_probe_ms += probe_interval_ms;
        }
#endif // HACK_PROBE_PERIODIC

        if (elapsed_ms >= next_display_ms) {
            malloc_accounting_display("periodic");
            printf("elapsed %d next %d int %d\n",
                elapsed_ms, next_display_ms, display_interval_ms);
            next_display_ms += display_interval_ms;
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

            cout << db.name << " [op] sync (completed " << i << " ops)" << endl;
            malloc_accounting_status();

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
            next_sync_ms += sync_interval_ms;

            fflush(stdout);
        } else {
            clock_prev = clock_op_completed;
        }
    }

    auto sync_started = chrono::steady_clock::now();
    if (have_done_insert_since_last_sync) {
      db.sync(true);
      have_done_insert_since_last_sync = false;
    }
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
    DbEnv *env;
    Db* pdb;
    dbstl::db_map<string, string> *huge_map;

public:
    static const string name;

  BerkeleyDBFacade(DbEnv *_env, Db *_pdb) : env(_env), pdb(_pdb) {
    huge_map = new dbstl::db_map<string, string>(pdb, env);
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

template< class DB >
void ycsbLoadAndRun(
    DB db,
    ycsbc::CoreWorkload& workload,
    int record_count,
    int num_ops,
    int sync_interval_ms,
    bool verbose) {

    ycsbLoad(db, workload, record_count, verbose);
    ycsbRun(db, workload, num_ops, sync_interval_ms, verbose);
    malloc_accounting_display("after experiment before teardown");
}

void dump_metadata(const char* workload_filename, const char* database_filename) {
  FILE* fp = fopen("/sys/fs/cgroup/memory/VeribetrfsExp/memory.limit_in_bytes", "r");
  char space[1000];
  char* line = fgets(space, sizeof(space), fp);
  fclose(fp);
  printf("metadata cgroups-memory.limit_in_bytes %s", line);

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

int main(int argc, char* argv[]) {
    bool verbose = false;
 
    if (argc < 3) {
      cerr << "Usage: " << argv[0] << " <workload.spec> ";
#ifdef _YCSB_VERIBETRFS
      cout << "<veribetrkv.img> ";
#endif
#ifdef _YCSB_ROCKS
      cout << "<rocks.db> ";
#endif
#ifdef _YCSB_BERKELEYDB
      cout << "<berkeley.db> ";
#endif
#ifdef _YCSB_KYOTO
      cout << "<kyoto.cbt> ";
#endif
      cout << "[--nop]" << endl;
      exit(-1);
    }

    std::string workload_filename(argv[1]);
    std::string database_filename(argv[2]);

    dump_metadata(workload_filename.c_str(), database_filename.c_str());

    bool do_nop = false;
    for (int i = 3; i < argc; i++) {
      if (string(argv[i]) == "--nop") {
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
    if (properties_map.find("syncintervalms") == properties_map.end()) {
        cerr << "error: spec must provide syncintervalms" << endl;
        exit(-1);
    }
    int sync_interval_ms = stoi(props["syncintervalms"]);
    int num_ops = stoi(props[ycsbc::CoreWorkload::OPERATION_COUNT_PROPERTY]);


    // == veribetrkv ==
    #ifdef _YCSB_VERIBETRFS
        Mkfs(database_filename);
        Application app(database_filename);
        VeribetrkvFacade db(app);
    
        ycsbLoadAndRun(db, *workload, record_count, num_ops, sync_interval_ms, verbose);
    #endif 

    // == rocksdb ==
    #ifdef _YCSB_ROCKS
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

        rocksdb::Status status = rocksdb::DB::Open(options, database_filename, &rocks_db);
        assert(status.ok());
        RocksdbFacade db(*rocks_db);

        ycsbLoadAndRun(db, *workload, record_count, num_ops, sync_interval_ms, verbose);
    #endif 

    // == kyotodb ==
    #ifdef _YCSB_KYOTO
        kyotocabinet::TreeDB tdb;
        tdb.open(database_filename,
                  kyotocabinet::TreeDB::OWRITER
                | kyotocabinet::TreeDB::OCREATE
                | kyotocabinet::TreeDB::ONOLOCK);
        KyotoFacade db(tdb);

        ycsbLoadAndRun(db, *workload, record_count, num_ops, sync_interval_ms, verbose);
    #endif 

    // == berkeleydb ==
    #ifdef _YCSB_BERKELEYDB
        static env_directory = dirname(database_filename.c_str());
        // (unsupported on macOS 10.14) std::filesystem::remove_all(rocksdb_path);
        //system(("rm -rf " + berkeley_path).c_str());

        DbEnv env(DB_CXX_NO_EXCEPTIONS);
        env.open(env_directory, DB_CREATE | DB_INIT_MPOOL, 0);
        Db* pdb;
        pdb = new Db(&env, DB_CXX_NO_EXCEPTIONS);
        pdb->open(NULL, database_filename.c_str(), NULL, DB_BTREE, DB_CREATE, 0);
        BerkeleyDBFacade db(&env, pdb);
        
        ycsbLoadAndRun(db, *workload, record_count, num_ops, sync_interval_ms, verbose);
    #endif 

    // == nop ==
    if (do_nop) {
        NopFacade db;

        ycsbLoadAndRun(db, *workload, record_count, num_ops, sync_interval_ms, verbose);
    }
}

