#include <unordered_map>
#include <execinfo.h>
#include <string.h>
#include <iostream>
#include <iomanip>
#include "leakfinder.h"
//#include <cxxabi.h>

#define max_frames 15
class Trace;
namespace std {
  template<>
    struct hash<Trace>
    {
      std::size_t operator()(const Trace& trace) const;
    };
}

class Trace {
  public:
    void* addrlist[max_frames+1];
    int addrlen;
    void capture() {
      addrlen = backtrace(addrlist, sizeof(addrlist) / sizeof(void*));
    }
    bool operator==(const Trace& other) const
    {
      return addrlen == other.addrlen
        && memcmp(addrlist, other.addrlist, sizeof(void*)*addrlen) == 0;
    }
};

std::size_t std::hash<Trace>::operator()(const Trace& trace) const
{
  std::size_t h = 7;
  for (int i=0; i<trace.addrlen; i++) {
     h ^= (long unsigned int) (trace.addrlist[i]);
  }
  return h;
}

typedef std::unordered_map<Trace, int> TraceMap;
static TraceMap traceMap;

void leakfinder_mark(int incr)
{
    Trace trace;
    trace.capture();
    if (traceMap.find(trace) == traceMap.end()) {
      traceMap.emplace(trace, 0);
    }
    traceMap.at(trace) += incr;
}

void leakfinder_report(int report_id)
{
  char fn[100];
  snprintf(fn, 90, "/tmp/trace-%d", report_id);
  FILE*fp = fopen(fn, "w");
  for (auto& x: traceMap) {
    const Trace& trace = x.first;
    fprintf(fp, "trace: count %d, has %d frames, hash %16lx\n",
        x.second, trace.addrlen, (unsigned long) std::hash<Trace>()(trace));
     //std::cout << "trace with " << x.first.addrlen << " frames: " << x.second << std::endl;
  }
  for (auto& x: traceMap) {
    const Trace& trace = x.first;
    fprintf(fp, "expanded: count %d, has %d frames, hash %16lx\n",
        x.second, trace.addrlen, (unsigned long) std::hash<Trace>()(trace));
    for (int i=0; i<trace.addrlen; i++) {
       fprintf(fp, "  %16lx\n", (long unsigned int) trace.addrlist[i]);
       //std::cout << "  " << std::hex << std::setw(16) << std::setfill('0') << trace.addrlist[i] << std::dec << std::endl;
    }
  }
  fclose(fp);
}
