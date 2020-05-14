include "NativeTypes.s.dfy"

module {:extern} Backtrace {
  import opened NativeTypes

  method {:extern "Backtrace_Compile", "Backtrace"} Backtrace() returns (bt: seq<uint64>)

  method {:extern "Backtrace_Compile", "FPrint"} FPrint(fd: uint64, bt: seq<uint64>)

  method {:extern "Backtrace_Compile", "DumpCollection"} DumpCollection(bts: map<seq<uint64>, uint64>)
}
