#include "bench/LinearMutableMap.h"

int main(int argc, char**argv) {
    if (argc != 3) {
        printf("invalid number of arguments\n");
        return -1;
    }
    uint64 seed = atol(argv[1]);
    bool dry = (strcmp(argv[2], "true") == 0);
    printf("METADATA title running with seed %llu dry run %d\n", (unsigned long long)seed, dry);
    MutableMapBench_Compile::__default::Run(seed, dry);
    return 0;
}
