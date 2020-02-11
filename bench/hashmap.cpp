//#include <DafnyRuntime.h>
//#include <Framework.h>
//#include <Bundle.i.h>
#include "MutableMapImpl.cpp"
#include <iostream>
#include <chrono>

using namespace _29_MutableMap_Compile;

#define NUM_INSERTS 1000000000

int main(int argc, char* argv[]) {
    const unsigned int num_ops = NUM_INSERTS;

    ResizingHashMap<uint64> m;
    m.__ctor(1024);

    auto clock_start = chrono::high_resolution_clock::now();
    for (uint64 v = 0; v < num_ops; v++) {
        m.Insert(v, v);
        if (v > 0) {
            m.Remove(v - 1);
        }
    }
    auto clock_end = chrono::high_resolution_clock::now();

    assert(m.Get(num_ops - 1).is_Some());

    long long bench_ns = std::chrono::duration_cast<std::chrono::nanoseconds>(clock_end - clock_start).count();

    double ops_per_sec = ((double) num_ops) / (((double) bench_ns) / 1000000000);

    std::cout << "ops\tops/s" << std::endl;
    std::cout << NUM_INSERTS << "\t" << ops_per_sec << std::endl;
}
