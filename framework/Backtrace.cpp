#include "Backtrace.h"
#include <execinfo.h>
#include <iostream>
#include <stdio.h>

using namespace std;

namespace Backtrace_Compile {
  DafnySequence<uint64> Backtrace()
  {
    DafnySequence<uint64> buffer(64);
    int length = backtrace((void **)buffer.ptr(), 64);
    return buffer.take(length);
  }

  void FPrint(uint64 fd, DafnySequence<uint64> bt)
  {
    fflush(stdout);
    backtrace_symbols_fd((void **)bt.ptr(), bt.length(), fd);
    fflush(stdout);
  }

  void DumpCollection(DafnyMap<DafnySequence<uint64>, uint64> bts)
  {
    for (auto it = bts.map.begin(); it != bts.map.end(); it++) {
      cout << "pkv-bucket backtrace occurs " << it->second << " times:\n";
      FPrint(1, it->first);
    }
  }
}
