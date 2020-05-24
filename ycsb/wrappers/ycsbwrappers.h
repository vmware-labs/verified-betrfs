#include <core_workload.h>

#include <vector>

namespace ycsbcwrappers {
    utils::Properties props_from(std::string filename);
    ycsbc::CoreWorkload* new_workload(utils::Properties& props);

    struct TxRead {
        const std::string table;
        const std::string key;
        const std::vector<std::string>* fields;

        TxRead(
            const std::string table,
            const std::string key,
            const std::vector<std::string>* fields) :
                table(table), key(key), fields(fields) {
        }

        ~TxRead() {
            if (this->fields != NULL) {
                delete this->fields;
            }
        }
    };

    struct TxInsert {
        const std::string table;
        const std::string key;
        const std::vector<std::pair<std::string, std::string>>* values;

        TxInsert(
            const std::string table,
            const std::string key,
            const std::vector<ycsbc::DB::KVPair>* values) :
                table(table), key(key), values(values) {
            assert(values != NULL);
        }
        
        ~TxInsert() {
            delete this->values;
        }
    };

    struct TxUpdate {
        const std::string table;
        const std::string key;
        const std::vector<std::pair<std::string, std::string>>* values;

        TxUpdate(
            const std::string table,
            const std::string key,
            const std::vector<ycsbc::DB::KVPair>* values) :
                table(table), key(key), values(values) {

            assert(values != NULL);
        }
        
        ~TxUpdate() {
            delete this->values;
        }
    };

    struct TxScan {
        const std::string table;
        const std::string key;
        int scan_length;
        const std::vector<std::string>* fields;

        TxScan(
            const std::string table,
            const std::string key,
            int len,
            const std::vector<std::string>* fields) :
          table(table), key(key), scan_length(len), fields(fields) {
        }
        
        ~TxScan() {
            if (this->fields != NULL) {
                delete this->fields;
            }
        }
    };

    const TxRead TransactionRead(ycsbc::CoreWorkload&workload);
    const TxInsert TransactionInsert(ycsbc::CoreWorkload&workload, bool load);
    const TxUpdate TransactionUpdate(ycsbc::CoreWorkload&workload);
    const TxScan TransactionScan(ycsbc::CoreWorkload&workload);
}
