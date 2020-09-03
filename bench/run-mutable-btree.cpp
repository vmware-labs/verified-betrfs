#include "LinearExtern.h"
#include "lib/DataStructures/LinearMutableBtree.i.h"

int main(int argc, char**argv) {
    if (argc != 4) {
        printf("invalid number of arguments\n");
        return -1;
    }
    uint64 seed = atol(argv[1]);
    uint64 ops = atol(argv[2]);
    bool dry = (strcmp(argv[3], "true") == 0);
    printf("METADATA title running %llu ops with seed %llu dry run %d\n", (unsigned long long)ops, (unsigned long long)seed, dry);
    MainModule_Compile::__default::Run(seed, ops, dry);
    return 0;
}
