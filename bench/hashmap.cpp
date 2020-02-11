//#include <DafnyRuntime.h>
//#include <Framework.h>
//#include <Bundle.i.h>
#include "MutableMapImpl.cpp"
#include <iostream>

using namespace _29_MutableMap_Compile;

int main(int argc, char* argv[]) {
    ResizingHashMap<uint64> m;
    m.__ctor(1024);

    for (uint64 v = 0; v <= 1000000; v++) {
        m.Insert(v, v);
    }

    cout << m.Get(5).is_Some() << endl;
}
