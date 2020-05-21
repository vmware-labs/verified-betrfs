#pragma once

#include "DafnyRuntime.h"
#include <chrono>

namespace LinearCongruentialGenerator_Compile {
  inline uint64_t steadyClockMillis() {
    auto now = std::chrono::steady_clock::now();
    return std::chrono::duration_cast<std::chrono::milliseconds>(
        now.time_since_epoch()).count();
  }

  inline void opaqueBlackhole(uint64_t value) {
    asm volatile("" : : "m"(value) : "memory");
  }

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
