// Hooks to collect IO rates from both Veribetrfs and Rocks

#pragma once

#include <stddef.h>
#include <x86intrin.h>

namespace IOAccounting {

class Record {
public:
  size_t read_count;
  size_t read_bytes;
  size_t write_count;
  size_t write_bytes;
};

extern Record record;

void report();
void reset_histograms();
void report_histograms();
void record_read_latency(unsigned long time_cycles);
void record_write_latency(unsigned long time_cycles);

} // namespace IOAccounting
