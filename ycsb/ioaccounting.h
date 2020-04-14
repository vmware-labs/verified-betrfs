// Hooks to collect IO rates from both Veribetrfs and Rocks

#pragma once

#include <stddef.h>

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

} // namespace IOAccounting
