
#include "ioaccounting.h"

#include <stdio.h>

namespace IOAccounting {

Record record;

void report() {
  printf("ioaccounting read_count %lu read_bytes %lu write_count %lu write_bytes %lu\n",
      (unsigned long) record.read_count,
      (unsigned long) record.read_bytes,
      (unsigned long) record.write_count,
      (unsigned long) record.write_bytes);
}

} // namespace IOAccounting
