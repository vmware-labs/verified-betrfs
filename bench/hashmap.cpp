//#include <DafnyRuntime.h>
//#include <Framework.h>
//#include <Bundle.i.h>
#include "MutableMapImpl.cpp"

using namespace _29_MutableMap_Compile;

int main(int argc, char* argv[]) {
    ResizingHashMap<uint64> m;

    for (uint64 v = 0; v <= 1000000; v++) {
        m.Insert(v, v);
    }
}
