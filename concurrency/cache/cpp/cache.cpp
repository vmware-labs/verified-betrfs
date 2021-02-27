// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

#include <shared_mutex>
#include <atomic>

using std::shared_mutex;

constexpr int CACHE_SIZE = (1 << 18);
constexpr int PAGE_SIZE = 4096;
constexpr int NUM_DISK_PAGES = (1 << 24);

constexpr uint32_t NO_CACHE_PAGE_ASSIGNED = 0xffffffff;

enum class Status {
  Empty,
  Clean,
  Dirty,
  Writing
};

struct CacheEntryMetadata {
  std::atomic<Status> status;
  uint32_t disk_idx;
};

volatile uint8_t cache_data[CACHE_SIZE][PAGE_SIZE];
volatile CacheEntryMetadata cache_metadata[CACHE_SIZE];
shared_mutex mutices[CACHE_SIZE];

constexpr CHUNK_SIZE = 64;
constexpr NUM_CHUNKS = CACHE_SIZE / CHUNK_SIZE;
constexpr CLEAN_AHEAD = NUM_CHUNKS / 3;

volatile bool recently_accessed[CACHE_SIZE];
thread_local uint32_t local_chunk = 0;
std::atomic<uint32_t> global_clockpointer = 0;

std::atomic<uint32_t> cache_idx_of_disk_idx[NUM_DISK_PAGES];

struct PageHandle {
  volatile uint8_t* data;
  volatile CacheEntryMetadata* metadata;

  PageHandle(uint32_t cache_idx) {
    data = &cache_data[cache_idx][0];
    metadata = &cache_metadata[cache_idx];
  }
};

void io_write_async(uint32_t cache_idx, uint32_t disk_idx);

void io_write_callback(uint32_t cache_idx, uint32_t disk_idx)
{
  cache_metadata[cache_idx].write_in_progress.store(Status::Dirty);
  mutices[cache_idx].unlock_shared();
}

void get_next_chunk()
{
  uint32_t l = global_clockpointer.fetch_add(1) % CACHE_SIZE;
  uint32_t c = (l + CLEAN_AHEAD) % CACHE_SIZE;

  for (int i = 0; i < CHUNK_SIZE; i++) {
    uint32_t cache_idx = c * CHUNK_SIZE + i;
    if (mutices[cache_idx].try_lock_shared()) {
      bool do_write = false;

      if (cache_metadata[cache_idx].status.load() == Status::Dirty
       && cache_metadata[cache_idx].write_in_progress.compare_exchange_strong(
                Status::Dirty, Status::Writing)
      {
        io_write_async(cache_idx, disk_idx);
      } else {
        mutices[cache_idx].unlock_shared();
      }
    }
  }

  local_chunk = l;
}

uint32_t lock_free_cache_idx()
{
  while (true) {
    for (int i = 0; i < CHUNK_SIZE; i++) {
      uint32_t cache_idx = local_chunk * CHUNK_SIZE + i;
      if (!recently_accessed[cache_idx]) {
        if (mutices[cache_idx].try_lock()) {
          if (cache_metadata[cache_idx].status == Status::Empty) {
            return cache_idx;
          }
          else if (cache_metadata[cache_idx].status == Status::Clean) {
            uint32_t disk_idx = cache_metadata[cache_idx].disk_idx;
            cache_idx_of_disk_idx[disk_idx].store(NO_CACHE_PAGE_ASSIGNED);
            return cache_idx;
          }
        } 
      }
    }

    for (int i = 0; i < CHUNK_SIZE; i++) {
      recently_accessed[i] = false;
    }

    next_chunk();
  }
}
