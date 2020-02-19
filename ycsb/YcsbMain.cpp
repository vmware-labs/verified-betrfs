#include <cstdlib>

#ifdef _YCSB_VERIBETRFS
#include "Application.h"
#endif

#include "core_workload.h"
#include "ycsbwrappers.h"

#include "hdrhist.hpp"

#ifdef _YCSB_ROCKS
#include "rocksdb/db.h"
#endif

#include <strstream>
//#include <filesystem>
#include <chrono>
#include <iostream>

using namespace std;

template< class DB >
inline void performYcsbRead(DB db, ycsbc::CoreWorkload& workload, bool verbose) {
    ycsbcwrappers::TxRead txread = ycsbcwrappers::TransactionRead(workload);
    if (!workload.read_all_fields()) {
        cerr << db.name << " error: not reading all fields unsupported" << endl;
        exit(-1);
    }
    if (verbose) {
        cerr << db.name << " [op] READ " << txread.table << " " << txread.key << " { all fields }" << endl;
    }
    // TODO use the table name?
    db.query(txread.key);
}

template< class DB >
inline void performYcsbInsert(DB db, ycsbc::CoreWorkload& workload, bool verbose) {
    ycsbcwrappers::TxInsert txinsert = ycsbcwrappers::TransactionInsert(workload);
    if (txinsert.values->size() != 1) {
        cerr << db.name << " error: only fieldcount=1 is supported" << endl;
        exit(-1);
    }
    const std::string& value = (*txinsert.values)[0].second;
    if (verbose) {
        cerr << db.name << " [op] INSERT " << txinsert.table << " " << txinsert.key << " " << value << endl;
    }
    // TODO use the table name?
    db.insert(txinsert.key, value);
}

template< class DB >
inline void performYcsbUpdate(DB db, ycsbc::CoreWorkload& workload, bool verbose) {
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
    // TODO use the table name?
    db.update(txupdate.key, value);
}

template< class DB >
void ycsbLoad(DB db, ycsbc::CoreWorkload& workload, int num_ops, bool verbose) {
    cerr << db.name << " [step] loading (num ops: " << num_ops << ")" << endl;

    auto clock_start = chrono::steady_clock::now();
    for (int i = 0; i < num_ops; ++i) {
        performYcsbInsert(db, workload, verbose);
    }

    cerr << db.name << " [step] sync" << endl;
    db.sync();

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

    cerr << db.name << " [step] running experiment (num ops: " << num_ops << ", sync interval " <<
        sync_interval_ms << "ms)" << endl;

    auto clock_start = chrono::steady_clock::now();
    auto clock_prev = clock_start;
    auto clock_last_sync = clock_start;

    for (int i = 0; i < num_ops; ++i) {
        auto next_operation = workload.NextOperation();
        switch (next_operation) {
            case ycsbc::READ:
                performYcsbRead(db, workload, verbose);
                break;
            case ycsbc::UPDATE:
                performYcsbUpdate(db, workload, verbose);
                break;
            case ycsbc::INSERT:
                performYcsbInsert(db, workload, verbose);
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

        if (std::chrono::duration_cast<std::chrono::milliseconds>(
            clock_op_completed - clock_last_sync).count() > sync_interval_ms) {

            db.sync();
            auto sync_completed = chrono::steady_clock::now();

            cerr << db.name << " [op] sync (completed " << i << " ops)" << endl;

            auto sync_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(
                sync_completed - clock_op_completed).count();
            sync_latency_hist.add_value(sync_duration);

            clock_last_sync = sync_completed;
            clock_prev = sync_completed;
        } else {
            clock_prev = clock_op_completed;
        }
    }

    auto clock_end = chrono::steady_clock::now();
    long long bench_ns = std::chrono::duration_cast<std::chrono::nanoseconds>(clock_end - clock_start).count();

    double ops_per_sec = ((double) num_ops) / (((double) bench_ns) / 1000000000);

    cerr << db.name << " [step] experiment complete" << endl;
    cout << "--\tthroughput\tduration(ns)\toperations\tops/s" << endl;
    cout << db.name << "\tthroughput\t" << bench_ns << "\t" << num_ops << "\t" << ops_per_sec << endl;

    {
        auto sync_summary = sync_latency_hist.summary();
        print_summary(sync_summary, db.name, "sync");

        for (auto op : operations) {
            auto op_summary = latency_hist[op.first]->summary();
            print_summary(op_summary, db.name, op.second);
        }
    }
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

    inline void sync() {
        app.Sync();
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

    inline void sync() {
        static struct rocksdb::FlushOptions foptions = rocksdb::FlushOptions();
        rocksdb::Status status = db.Flush(foptions);
        assert(status.ok());
    }
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

    inline void sync() {
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
}

int main(int argc, char* argv[]) {
    bool verbose = false;
 
    if (argc < 3) {
        cerr << "error: expects two arguments: the workload spec, and the persistent data directory" << endl;
        exit(-1);
    }

    std::string workload_filename(argv[1]);
    std::string base_directory(argv[2]);
    // (unsupported on macOS 10.14) std::filesystem::create_directory(base_directory);
    // check that base_directory is empty
    int status = std::system(("[ \"$(ls -A " + base_directory + ")\" ]").c_str());
    if (status == 0) {
        cerr << "error: " << base_directory << " appears to be non-empty";
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
    if (properties_map.find("syncintervalms") == properties_map.end()) {
        cerr << "error: spec must provide syncintervalms" << endl;
        exit(-1);
    }
    int sync_interval_ms = stoi(props["syncintervalms"]);
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
    
        ycsbLoadAndRun(db, *workload, record_count, num_ops, sync_interval_ms, verbose);
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

        // disabled - we let rocks use the page cache
        // options.use_direct_reads = true;
        // options.use_direct_io_for_flush_and_compaction = true;

        rocksdb::Status status = rocksdb::DB::Open(options, rocksdb_path, &rocks_db);
        assert(status.ok());
        RocksdbFacade db(*rocks_db);

        ycsbLoadAndRun(db, *workload, record_count, num_ops, sync_interval_ms, verbose);
    #endif 
    }


    // == nop ==
    if (do_nop) {
        NopFacade db;

        ycsbLoadAndRun(db, *workload, record_count, num_ops, sync_interval_ms, verbose);
    }
}

