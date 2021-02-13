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
  Dirty
};

struct CacheEntryMetadata {
  Status status;
  uint32_t disk_idx;
};

volatile uint8_t cache_data[CACHE_SIZE][PAGE_SIZE];
volatile CacheEntryMetadata cache_metadata[CACHE_SIZE];
shared_mutex mutices[CACHE_SIZE];

volatile bool recently_accessed[CACHE_SIZE];
thread_local uint32_t clockpointer = 0;

std::atomic<uint32_t> cache_idx_of_disk_idx[NUM_DISK_PAGES];

struct PageHandle {
  volatile uint8_t* data;
  volatile CacheEntryMetadata* metadata;

  PageHandle(uint32_t cache_idx) {
    data = &cache_data[cache_idx][0];
    metadata = &cache_metadata[cache_idx];
  }
};

// Synchronously read page from disk into cache_data[cache_idx]
void read_page(uint32_t cache_idx, uint32_t disk_page);

// Synchronously write page from cache_data[cache_idx] onto disk
void write_page(uint32_t cache_idx, uint32_t disk_page);

// Returns a cache entry that is empty, clean, or can be evicted
uint32_t lock_free_cache_idx() {
  while (true) {
    if (recently_accessed[clockpointer]) {
      recently_accessed[clockpointer] = true;

      clockpointer++;
      if (clockpointer == CACHE_SIZE) {
        clockpointer = 0;
      }
    } else {
      uint32_t cache_idx = clockpointer;

      clockpointer++;
      if (clockpointer == CACHE_SIZE) {
        clockpointer = 0;
      }

      if (mutices[cache_idx].try_lock()) {
        if (cache_metadata[cache_idx].status == Status::Dirty) {
          write_page(cache_idx, cache_metadata[cache_idx].disk_idx);
          cache_idx_of_disk_idx[cache_metadata[cache_idx].disk_idx] = NO_CACHE_PAGE_ASSIGNED;
        }
        cache_metadata[cache_idx].status = Status::Empty;

        return cache_idx;
      }
    }
  }
}

// Acquire a handle on a page
PageHandle acquire_disk_page(uint32_t disk_page) {
beginning:
  
  uint32_t cache_idx = cache_idx_of_disk_idx[disk_page].load();

  if (cache_idx == NO_CACHE_PAGE_ASSIGNED) {
    cache_idx = lock_free_cache_idx();

    uint32_t expected = NO_CACHE_PAGE_ASSIGNED;
    bool cas_success =
        cache_idx_of_disk_idx[disk_page].compare_exchange_strong(expected, cache_idx);

    if (cas_success) {

      read_page(cache_idx, disk_page);
      cache_metadata[cache_idx].status = Status::Clean;
      cache_metadata[cache_idx].disk_idx = disk_page;

      return PageHandle(cache_idx);
    } else {
      mutices[cache_idx].unlock();
      goto beginning;
    }
  } else {
    bool lock_succ = mutices[cache_idx].try_lock();

    if (!lock_succ) {
      goto beginning;
    }

    if (!(
      cache_metadata[cache_idx].status != Status::Empty &&
      cache_metadata[cache_idx].disk_idx == disk_page
    )) {
      mutices[cache_idx].unlock();
      goto beginning;
    }

    return PageHandle(cache_idx);
  }
}

void release_handle(PageHandle handle) {
  uint32_t cache_idx = handle.metadata - cache_metadata;
  recently_accessed[cache_idx] = true;
  mutices[cache_idx].unlock();
}

void sync_all() {
  // TODO this should be done async
  for (int i = 0; i < CACHE_SIZE; i++) {
    mutices[i].lock_shared();
    if (cache_metadata[i].status == Status::Dirty) {
      write_page(i, cache_metadata[i].disk_idx);
      cache_metadata[i].status = Status::Clean;
    }
    mutices[i].unlock_shared();
  }
}
