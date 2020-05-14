#pragma once

#include "DafnyRuntime.h"

namespace Backtrace_Compile {
  DafnySequence<uint64> Backtrace();

  void FPrint(uint64 fd, DafnySequence<uint64> bt);

  void DumpCollection(DafnyMap<DafnySequence<uint64>, uint64> bts);
}
