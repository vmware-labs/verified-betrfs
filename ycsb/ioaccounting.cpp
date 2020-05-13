
#include "ioaccounting.h"

#include <stdio.h>
#include <iostream>
#include "hdrhist.hpp"

namespace IOAccounting {

Record record;
HDRHist read_hist;
HDRHist write_hist;
uint64_t slow_reads = 0;
uint64_t slow_writes = 0;
const uint64_t slow_cycles_threshold = 100000;   // ~45usec: way longer than anything in cache; probably includes all disk IO

void dump_ccdf_to_stdout(const HDRHist& hist) {
  auto upper_bound = hist.ccdf_upper_bound();
  for (auto ccdf_el = upper_bound.next();
      ccdf_el.has_value();
      ccdf_el = upper_bound.next()) {
    std::cout << " " << ccdf_el->value << ":" << ccdf_el->fraction << ":" << ccdf_el->count;
  }
  std::cout << std::endl;
}

void report() {
  printf("ioaccounting read_count %lu read_bytes %lu write_count %lu write_bytes %lu\n",
      (unsigned long) record.read_count,
      (unsigned long) record.read_bytes,
      (unsigned long) record.write_count,
      (unsigned long) record.write_bytes);
  printf("ioaccounting-slow threshhold-cycles %lu slow_reads %lu slow_writes %lu\n",
      (unsigned long) slow_cycles_threshold,
      (unsigned long) slow_reads,
      (unsigned long) slow_writes);
}

void report_histograms() {
  std::cout << "io-latency read";
  dump_ccdf_to_stdout(read_hist);
  std::cout << "io-latency write";
  dump_ccdf_to_stdout(write_hist);
}

void reset_histograms()
{
  read_hist = HDRHist();
  write_hist = HDRHist();
}

void record_read_latency(unsigned long time_cycles) {
  read_hist.add_value(time_cycles);
  if (time_cycles > slow_cycles_threshold) {
    slow_reads += 1;
  }
}

void record_write_latency(unsigned long time_cycles) {
  write_hist.add_value(time_cycles);
  if (time_cycles > slow_cycles_threshold) {
    slow_writes += 1;
  }
}

} // namespace IOAccounting
