#include "Application.h"

#include "core_workload.h"
#include "ycsbwrappers.h"

#include "hdrhist.hpp"

#include <strstream>
#include <chrono>

using namespace std;

inline void performYcsbRead(Application& app, ycsbc::CoreWorkload& workload, bool verbose) {
    ycsbcwrappers::TxRead txread = ycsbcwrappers::TransactionRead(workload);
    if (!workload.read_all_fields()) {
        cerr << "error: not reading all fields unsupported" << endl;
        exit(-1);
    }
    if (verbose) {
        cerr << "[op] READ " << txread.table << " " << txread.key << " { all fields }" << endl;
    }
    // TODO use the table name?
    app.Query(txread.key);
}

inline void performYcsbInsert(Application& app, ycsbc::CoreWorkload& workload, bool verbose) {
    ycsbcwrappers::TxInsert txinsert = ycsbcwrappers::TransactionInsert(workload);
    strstream valuestream;
    for (const ycsbc::DB::KVPair& kv : *txinsert.values) {
        valuestream << kv.first << ":" << kv.second << ",";
    }
    valuestream << ends;
    if (verbose) {
        cerr << "[op] INSERT " << txinsert.table << " " << txinsert.key << " {" << valuestream.str() << "}" << endl;
    }
    // TODO use the table name?
    app.Insert(txinsert.key, valuestream.str());
    valuestream.freeze(false); // ensure deallocation of the buffer
}

inline void performYcsbUpdate(Application& app, ycsbc::CoreWorkload& workload, bool verbose) {
    ycsbcwrappers::TxUpdate txupdate = ycsbcwrappers::TransactionUpdate(workload);
    if (!workload.write_all_fields()) {
        cerr << "error: not writing all fields unsupported" << endl;
        exit(-1);
    }
    strstream valuestream;
    for (const ycsbc::DB::KVPair& kv : *txupdate.values) {
        valuestream << kv.first << ":" << kv.second << ",";
    }
    valuestream << ends;
    if (verbose) {
        cerr << "[op] UPDATE " << txupdate.table << " " << txupdate.key << " {" << valuestream.str() << "}" << endl;
    }
    // TODO use the table name?
    app.Insert(txupdate.key, valuestream.str());
    valuestream.freeze(false); // ensure deallocation of the buffer
}

void ycsbLoad(Application& app, ycsbc::CoreWorkload& workload, int num_ops, bool verbose) {
    cerr << "[step] loading (num ops: " << num_ops << ")" << endl;

    for (int i = 0; i < num_ops; ++i) {
        performYcsbInsert(app, workload, verbose);
    }

    cerr << "[step] loading complete" << endl;
}

void ycsbRun(Application& app, ycsbc::CoreWorkload& workload, int num_ops, bool verbose) {
    cerr << "[step] running experiment (num ops: " << num_ops << ")" << endl;

    // TODO: how frequently should we sync?
 
    auto clock_start = chrono::high_resolution_clock::now();
    auto clock_prev = clock_start;

    for (int i = 0; i < num_ops; ++i) {
        auto next_operation = workload.NextOperation();
        switch (next_operation) {
            case ycsbc::READ:
                performYcsbRead(app, workload, verbose);
                break;
            case ycsbc::UPDATE:
                performYcsbUpdate(app, workload, verbose);
                break;
            case ycsbc::INSERT:
                performYcsbInsert(app, workload, verbose);
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

        clock_prev = chrono::high_resolution_clock::now();
    }

    auto clock_end = chrono::high_resolution_clock::now();
    long long bench_ns = std::chrono::duration_cast<std::chrono::nanoseconds>(clock_end - clock_start).count();

    double ops_per_sec = ((double) num_ops) / (((double) bench_ns) / 1000000000);

    cerr << "[step] experiment complete" << endl;
    cout << "duration(ns)\toperations\tops/s" << endl;
    cout << bench_ns << "\t" << num_ops << "\t" << ops_per_sec << endl;
}

int main(int argc, char* argv[]) {
    bool verbose = false;

    if (argc != 2) {
        cerr << "error: expects one argument: the workload spec" << endl;
        exit(-1);
    }

    std::string workload_filename(argv[1]);

    ClearIfExists();
    Mkfs();

    Application app;

    utils::Properties props = ycsbcwrappers::props_from(workload_filename);
    unique_ptr<ycsbc::CoreWorkload> workload(ycsbcwrappers::new_workload(props));
    int record_count = stoi(props[ycsbc::CoreWorkload::RECORD_COUNT_PROPERTY]);

    ycsbLoad(app, *workload, record_count, verbose);

    cerr << "[step] sync" << endl;
    app.Sync();

    int num_ops = stoi(props[ycsbc::CoreWorkload::OPERATION_COUNT_PROPERTY]);

    ycsbRun(app, *workload, num_ops, verbose);
}

