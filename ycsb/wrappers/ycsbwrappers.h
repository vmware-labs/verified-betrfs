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
            delete this->fields;
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
        }
        
        ~TxInsert() {
            delete this->values;
        }
    };

    const TxRead TransactionRead(ycsbc::CoreWorkload&workload);
    const TxInsert TransactionInsert(ycsbc::CoreWorkload&workload);
}
