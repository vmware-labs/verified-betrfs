#ifndef NR_CONSTANTS_H
#define NR_CONSTANTS_H

#include <cinttypes>

const uint8_t NUM_THREADS = 4;
const uint8_t NUM_REPLICAS = 2;
const uint8_t THREADS_PER_REPLICA = NUM_THREADS / NUM_REPLICAS;

#endif