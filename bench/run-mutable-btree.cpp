#include "lib/DataStructures/MutableBtree.i.h"

int main(int argc, char**argv) {
    if (argc != 2) {
        printf("invalid number of arguments\n");
        return -1;
    }
    uint64 ops = atoi(argv[1]);
    printf("running %llu ops\n", ops);
    MainModule_Compile::__default::Run(ops);
    return 0;
}
