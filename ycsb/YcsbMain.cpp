#include "Application.h"

#include "core_workload.h"
#include "ycsbwrappers.h"

#include <strstream>

using namespace std;

void load(Application& app, ycsbc::CoreWorkload& workload, int num_ops, bool verbose) {
    cerr << "[step] loading (num ops: " << num_ops << ")" << endl;

    for (int i = 0; i < num_ops; ++i) {
        ycsbcwrappers::TxInsert txinsert = ycsbcwrappers::TransactionInsert(workload);
        strstream valuestream;
        for (const ycsbc::DB::KVPair& kv : *txinsert.values) {
            valuestream << kv.first << ":" << kv.second << ",";
        }
        valuestream << ends;
        if (verbose) {
            cerr << "[op] [insert] " << txinsert.table << " " << txinsert.key << " {" << valuestream.str() << "}" << endl;
        }
        app.Insert(txinsert.key, valuestream.str());
        valuestream.freeze(false); // ensure deallocation of the buffer
    }

    cerr << "[step] loading complete" << endl;
}

int main(int argc, char* argv[]) {
    bool verbose = false;

    if (argc != 2) {
        cerr << "expects one argument: the workload spec" << endl;
        exit(-1);
    }

    std::string workload_filename(argv[1]);

    ClearIfExists();
    Mkfs();

    Application app;

    utils::Properties props = ycsbcwrappers::props_from(workload_filename);
    unique_ptr<ycsbc::CoreWorkload> workload(ycsbcwrappers::new_workload(props));
    int num_ops = stoi(props[ycsbc::CoreWorkload::RECORD_COUNT_PROPERTY]);

    load(app, *workload, num_ops, verbose);

    cerr << "[step] sync" << endl;
    app.Sync();
}

