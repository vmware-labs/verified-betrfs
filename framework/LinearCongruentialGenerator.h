#pragma once

#include "DafnyRuntime.h"

namespace LinearCongruentialGenerator_Compile {
  class LCG {
    uint64_t seed;

    public:
    LCG(uint64_t seed) : seed(seed) { }

    inline uint64_t next() {
      seed = ((
          (seed * 6364136223846793005) & 0xffffffffffffffff)
          + 1442695040888963407) & 0xffffffffffffffff;
      return seed;
    }
  };
} 
