#include "ycsbwrappers.h"

#include <iostream>
#include <string>

#include "core_workload.h"
#include "utils.h"

utils::Properties ycsbcwrappers::props_from(std::string filename) {
    utils::Properties props;
    std::ifstream input(filename);
    props.Load(input);
    return props;
}

ycsbc::CoreWorkload* ycsbcwrappers::new_workload(utils::Properties& props) {
    ycsbc::CoreWorkload* wl = new ycsbc::CoreWorkload;
    wl->Init(props);
    return wl;
}

const ycsbcwrappers::TxRead ycsbcwrappers::TransactionRead(ycsbc::CoreWorkload&workload) {
    const std::string table = workload.NextTable();
    const std::string key = workload.NextTransactionKey();
    if (!workload.read_all_fields()) {
        std::vector<std::string>* fields = new std::vector<std::string>;
        fields->push_back("field" + workload.NextFieldName());
        return TxRead(table, key, fields);
    } else {
        return TxRead(table, key, NULL);
    }
}

const ycsbcwrappers::TxInsert ycsbcwrappers::TransactionInsert(ycsbc::CoreWorkload&workload, bool load) {
    const std::string &table = workload.NextTable();
    const std::string &key = load ? workload.NextSequenceKey() : workload.NextTransactionKey();
    std::vector<ycsbc::DB::KVPair>* values = new std::vector<ycsbc::DB::KVPair>();
    values->reserve(16);
    workload.BuildValues(*values);
    return TxInsert(table, key, values);
} 

const ycsbcwrappers::TxUpdate ycsbcwrappers::TransactionUpdate(ycsbc::CoreWorkload&workload) {
    const std::string &table = workload.NextTable();
    const std::string &key = workload.NextTransactionKey();
    std::vector<ycsbc::DB::KVPair>* values = new std::vector<ycsbc::DB::KVPair>();
    values->reserve(16);
    if (workload.write_all_fields()) {
        workload.BuildValues(*values);
    } else {
        workload.BuildUpdate(*values);
    }
    return TxUpdate(table, key, values);
} 

const ycsbcwrappers::TxScan ycsbcwrappers::TransactionScan(ycsbc::CoreWorkload&workload) {
    const std::string &table = workload.NextTable();
    const std::string &key = workload.NextSequenceKey();
    int len = workload.NextScanLength();
    if (!workload.read_all_fields()) {
        std::vector<std::string>* fields = new std::vector<std::string>;
        fields->push_back("field" + workload.NextFieldName());
        return TxScan(table, key, len, fields);
    } else {
        return TxScan(table, key, len, NULL);
    }
} 
