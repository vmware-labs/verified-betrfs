// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: Apache-2.0

/*
 * clockcache.c --
 *
 *     This file contains the implementation for a concurrent clock cache.
 */

#include <type_traits>
#include <cstdint>

extern "C" {

#define bool uint32_t

#include "platform.h"
#include "clockcache.h"

#undef bool

}

#include <string>
#include <iostream>
#include "veri/Extern.h"
#include "veri/DiskExtern.h"
#include "veri/LinearExtern.h"
#include "veri/Application.i.h"


// Number of entries to clean/evict/get_free in a per-thread batch
#define CC_ENTRIES_PER_BATCH 64

/* number of events to poll for during clockcache_wait */
#define CC_DEFAULT_MAX_IO_EVENTS 32

/*
 * clockcache_log, etc. are used to write an output of cache operations to a
 * log file for debugging purposes. If CC_LOG is set, then all output is
 * written, if ADDR_TRACING is set, then only operations which affect entries
 * with either entry_number TRACE_ENTRY or address TRACE_ADDR are written.
 *
 * clockcache_log_stream should be called between platform_open_log_stream
 * and platform_close_log_stream.
 *
 * Note: these are debug functions, so calling platform_get_tid() potentially
 * repeatedly is ok.
 */
#ifdef ADDR_TRACING
#define clockcache_log(addr, entry, message, ...)                       \
   do {                                                                 \
      if (addr == TRACE_ADDR || entry == TRACE_ENTRY) {                 \
         platform_handle_log(cc->logfile, "(%lu) "message,              \
               platform_get_tid(), ##__VA_ARGS__);                      \
      }                                                                 \
   } while(0)
#define clockcache_log_stream(addr, entry, message, ...)                \
   do {                                                                 \
      if (addr == TRACE_ADDR || entry == TRACE_ENTRY) {                 \
         platform_log_stream("(%lu) "message, platform_get_tid(),       \
               ##__VA_ARGS__);                                          \
      }                                                                 \
   } while(0)
#else
#ifdef CC_LOG
#define clockcache_log(addr, entry, message, ...)                       \
   do {                                                                 \
      (void)(addr);                                                     \
      platform_handle_log(cc->logfile, "(%lu) "message,                 \
               platform_get_tid(), ##__VA_ARGS__);                      \
   } while (0)

#define clockcache_log_stream(addr, entry, message, ...)                \
   platform_log_stream("(%lu) "message, platform_get_tid(),             \
               ##__VA_ARGS__);
#else
#define clockcache_log(addr, entry, message, ...) \
   do {                                           \
      (void)(addr);                               \
      (void)(entry);                              \
      (void)(message);                            \
   } while (0)
#define clockcache_log_stream(addr, entry, message, ...) \
   do {                                                  \
      (void)(addr);                                      \
      (void)(entry);                                     \
      (void)(message);                                   \
   } while (0)
#endif
#endif

#if defined CC_LOG || defined ADDR_TRACING
#define clockcache_open_log_stream() platform_open_log_stream()
#else
#define clockcache_open_log_stream()
#endif

#if defined CC_LOG || defined ADDR_TRACING
#define clockcache_close_log_stream() platform_close_log_stream(cc->logfile)
#else
#define clockcache_close_log_stream()
#endif


// clang-format off
page_handle *clockcache_alloc                (clockcache *cc, uint64 addr, page_type type);
uint32_t         clockcache_dealloc              (clockcache *cc, uint64 addr, page_type type);
uint8        clockcache_get_allocator_ref    (clockcache *cc, uint64 addr);
page_handle *clockcache_get                  (clockcache *cc, uint64 addr, uint32_t blocking, page_type type);
cache_async_result clockcache_get_async      (clockcache *cc, uint64 addr, page_type type, cache_async_ctxt *ctxt);
void         clockcache_async_done           (clockcache *cc, page_type type, cache_async_ctxt *ctxt);
void         clockcache_unget                (clockcache *cc, page_handle *page);
uint32_t         clockcache_claim                (clockcache *cc, page_handle *page);
void         clockcache_unclaim              (clockcache *cc, page_handle *page);
void         clockcache_lock                 (clockcache *cc, page_handle *page);
void         clockcache_unlock               (clockcache *cc, page_handle *page);
void         clockcache_prefetch(clockcache *cc, uint64 addr, page_type type);
void         clockcache_mark_dirty           (clockcache *cc, page_handle *page);
void         clockcache_pin                  (clockcache *cc, page_handle *page);
void         clockcache_unpin                (clockcache *cc, page_handle *page);

void         clockcache_page_sync            (clockcache *cc, page_handle *page, uint32_t is_blocking, page_type type);
void         clockcache_extent_sync          (clockcache *cc, uint64 addr, uint64 *pages_outstanding);

void         clockcache_flush                (clockcache *cc);
int          clockcache_evict_all            (clockcache *cc, uint32_t ignore_pinned);
void         clockcache_wait                 (clockcache *cc);

uint64       clockcache_get_page_size        (const clockcache *cc);
uint64       clockcache_get_extent_size      (const clockcache *cc);

void         clockcache_assert_ungot         (clockcache *cc, uint64 addr);
void         clockcache_assert_noleaks       (clockcache *cc);
void         clockcache_assert_no_locks_held (clockcache *cc);
void         clockcache_print                (clockcache *cc);
uint32_t         clockcache_page_valid           (clockcache *cc, uint64 addr);
void         clockcache_validate_page        (clockcache *cc, page_handle *page, uint64 addr);

void         clockcache_print_stats          (clockcache *cc);
void         clockcache_io_stats             (clockcache *cc, uint64 *read_bytes, uint64 *write_bytes);
void         clockcache_reset_stats          (clockcache *cc);

uint32       clockcache_count_dirty          (clockcache *cc);
uint16       clockcache_get_read_ref         (clockcache *cc, page_handle *page);

uint32_t         clockcache_present              (clockcache *cc, page_handle *page);
static void  clockcache_enable_sync_get      (clockcache *cc, uint32_t enabled);
allocator *  clockcache_allocator            (clockcache *cc);

static cache_ops clockcache_ops = {
   .page_alloc        = (page_alloc_fn)        clockcache_alloc,
   .page_dealloc      = (page_dealloc_fn)      clockcache_dealloc,
   .page_get_ref      = (page_get_ref_fn)      clockcache_get_allocator_ref,
   .page_get          = (page_get_fn)          clockcache_get,
   .page_get_async    = (page_get_async_fn)    clockcache_get_async,
   .page_async_done   = (page_async_done_fn)   clockcache_async_done,
   .page_unget        = (page_unget_fn)        clockcache_unget,
   .page_claim        = (page_claim_fn)        clockcache_claim,
   .page_unclaim      = (page_unclaim_fn)      clockcache_unclaim,
   .page_lock         = (page_lock_fn)         clockcache_lock,
   .page_unlock       = (page_unlock_fn)       clockcache_unlock,
   .page_prefetch     = (page_prefetch_fn)     clockcache_prefetch,
   .page_mark_dirty   = (page_mark_dirty_fn)   clockcache_mark_dirty,
   .page_pin          = (page_pin_fn)          clockcache_pin,
   .page_unpin        = (page_unpin_fn)        clockcache_unpin,
   .page_sync         = (page_sync_fn)         clockcache_page_sync,
   .extent_sync       = (extent_sync_fn)       clockcache_extent_sync,
   .flush             = (flush_fn)             clockcache_flush,
   .evict             = (evict_fn)             clockcache_evict_all,
   .cleanup           = (cleanup_fn)           clockcache_wait,
   .get_page_size     = (get_cache_size_fn)    clockcache_get_page_size,
   .get_extent_size   = (get_cache_size_fn)    clockcache_get_extent_size,
   .assert_ungot      = (assert_ungot_fn)      clockcache_assert_ungot,
   .assert_free       = (assert_free_fn)       clockcache_assert_no_locks_held,
   .assert_noleaks    = (assert_noleaks)       clockcache_assert_noleaks,
   .print             = (print_fn)             clockcache_print,
   .print_stats       = (print_fn)             clockcache_print_stats,
   .io_stats          = (io_stats_fn)          clockcache_io_stats,
   .reset_stats       = (reset_stats_fn)       clockcache_reset_stats,
   .page_valid        = (page_valid_fn)        clockcache_page_valid,
   .validate_page     = (validate_page_fn)     clockcache_validate_page,

   .count_dirty       = (count_dirty_fn)       clockcache_count_dirty,
   .page_get_read_ref = (page_get_read_ref_fn) clockcache_get_read_ref,

   .cache_present     = (cache_present_fn)     clockcache_present,
   .enable_sync_get   = (enable_sync_get_fn)   clockcache_enable_sync_get,
   .cache_allocator   = (cache_allocator_fn)   clockcache_allocator,
};
// clang-format on

[[ noreturn ]]
void fail(std::string err)
{
  std::cout << "fatal error: " << err << std::endl;
  exit(1);
}

void constant_check(std::string err, uint64 a, uint64 b)
{
  if (a != b) { 
    std::cout << "fatal error: constant config doesn't match: "
        << err << " (got " << a << " and " << b << ")" << std::endl;
    exit(1);
  }
}

/*
 *-----------------------------------------------------------------------------
 *
 * clockcache_config_init --
 *
 *      Initialize clockcache config values
 *
 *-----------------------------------------------------------------------------
 */

void clockcache_config_init(clockcache_config *cache_cfg,
                            uint64             page_size,
                            uint64             extent_size,
                            uint64             capacity,
                            char              *cache_logfile,
                            uint64             use_stats)
{
   int rc;
   ZERO_CONTENTS(cache_cfg);

   cache_cfg->page_size     = page_size;
   cache_cfg->extent_size   = extent_size;
   cache_cfg->capacity      = capacity;
   cache_cfg->log_page_size = 63 - __builtin_clzll(page_size);
   cache_cfg->page_capacity = capacity / page_size;
   cache_cfg->use_stats     = use_stats;

   rc = snprintf(cache_cfg->logfile, MAX_STRING_LENGTH, "%s", cache_logfile);
   platform_assert(rc < MAX_STRING_LENGTH);
}

static inline uint64
clockcache_multiply_by_page_size(clockcache *cc,
                                 uint64      addr)
{
   return addr << cc->cfg->log_page_size;
}

static inline uint64
clockcache_divide_by_page_size(clockcache *cc,
                               uint64      addr)
{
   return addr >> cc->cfg->log_page_size;
}

using CacheType = CacheTypes_ON_TheAIO__Compile::Cache;
using LocalType = CacheTypes_ON_TheAIO__Compile::LocalState;
using PHType = CacheOps_ON_TheAIO__Compile::PageHandleIdx;

namespace InstantiatedDiskInterface {
  int fd;
}

struct inner_cache {
  CacheType ct;

  LocalType PLATFORM_CACHELINE_ALIGNED per_thread[MAX_THREADS];
};

#define AppNamespace Application_ON_TheAIO__Compile::__default
#define CacheOpsNamespace CacheOps_ON_TheAIO__Compile::__default

platform_status
clockcache_init(clockcache           *cc,     // OUT
                clockcache_config    *cfg,    // IN
                io_handle            *io,     // IN
                allocator            *al,     // IN
                char                 *name,   // IN
                task_system          *ts,  // IN
                platform_heap_handle  hh,     // IN
                platform_heap_id      hid,    // IN
                platform_module_id    mid)    // IN
{
  ZERO_CONTENTS(cc);

  cc->cfg = cfg;
  cc->super.ops = &clockcache_ops;
  cc->al = al;

  cc->cfg->pages_per_extent
      = clockcache_divide_by_page_size(cc, cc->cfg->extent_size);

  uint64 allocator_page_capacity
      = clockcache_divide_by_page_size(cc, allocator_get_capacity(al));

  Constants_Compile::PreConfig pc(0, 0, 0, 0);
  pc.cache__size = cc->cfg->page_capacity;
  pc.num__disk__pages = allocator_page_capacity;
  pc.pages__per__extent = cc->cfg->pages_per_extent;
  pc.num__io__slots = ((laio_handle*)io)->cfg->async_queue_size;

  if (!pc.WF()) {
    std::cout << "clockcache PreConfig not well-formed" << std::endl;
    std::cout << "cache_size: " << pc.cache__size;
    exit(1);
  }

  constant_check("page_size", 1 << cc->cfg->log_page_size,
      PageSizeConstant_Compile::__default::PageSize64());

  constant_check("chunk size", CC_ENTRIES_PER_BATCH,
      Constants_Compile::__default::CHUNK__SIZE__32());

  constant_check("rc width", CC_RC_WIDTH,
      Constants_Compile::__default::RC__WIDTH__64());

  constant_check("clean ahead", 512,
      Constants_Compile::__default::CLEAN__AHEAD__64());

  constant_check("PLATFORM_CACHELINE_SIZE", PLATFORM_CACHELINE_SIZE,
      Constants_Compile::__default::PLATFORM__CACHELINE__SIZE__64());

  InstantiatedDiskInterface::fd = ((laio_handle*)io)->fd;

  cc->ic = new inner_cache();

  cc->ic->ct = AppNamespace::init(pc);
  for (int i = 0; i < MAX_THREADS; i++) {
    cc->ic->per_thread[i] = AppNamespace::init__thread__local__state(i);
  }

  return STATUS_OK;
}

inline LocalType& get_local_state(clockcache* cc)
{
  const threadid tid = platform_get_tid();
  return cc->ic->per_thread[tid];
}

inline page_handle* to_page_handle_pointer(clockcache* cc, PHType ph)
{
  uint64 ci = ph.cache__idx;
  void* p = &((cc->ic->ct.status__idx__array).ptr[ci].a.page__handle.v);
  return (page_handle *) p; // lol
}

inline PHType page_handle_index(clockcache* cc, page_handle* ph)
{
  uint64_t off1 = offsetof(
    //decltype((*cc->ic->ct.status__idx__array)[0]),
    LinearMaybe::maybe<CacheTypes_ON_TheAIO__Compile::StatusIdx>,
    a);

  uint64_t off2 = offsetof(
    decltype((cc->ic->ct.status__idx__array).ptr[0].a),
    page__handle);

  uint64_t off3 = offsetof(
    decltype((cc->ic->ct.status__idx__array).ptr[0].a.page__handle),
    v);

  uint64_t off = off1 + off2 + off3;

  uint64_t ci = (((char*)ph) - off - (char*)(void*)(&((cc->ic->ct.status__idx__array).ptr[0]))) /
      sizeof(decltype((cc->ic->ct.status__idx__array).ptr[0]));

  PHType pht = PHType(ci);

  //if (to_page_handle_pointer(cc, pht) != ph) {
  //  fail("whoops");
  //}

  return pht;
}

void
clockcache_deinit(clockcache *cc) // IN/OUT
{
  //fail("deinit");
}

/*
 *-----------------------------------------------------------------------------
 *
 * clockcache_flush --
 *
 *      Issues writeback for all page in the cache.
 *
 *      Asserts that there are no pins, read locks, claims or write locks.
 *
 *-----------------------------------------------------------------------------
 */

void
clockcache_flush(clockcache *cc)
{
  CacheOpsNamespace::flush(cc->ic->ct, get_local_state(cc));
}

/*
 *-----------------------------------------------------------------------------
 *
 * clockcache_evict_all --
 *
 *      evicts all the pages.
 *
 *-----------------------------------------------------------------------------
 */

int
clockcache_evict_all(clockcache *cc, uint32_t ignore_pinned_pages)
{
  fail("evict_all");
}

/*
 *----------------------------------------------------------------------
 *
 * clockcache_alloc --
 *
 *      Given a disk_addr, allocate entry in the cache and return its page with
 *      a write lock.
 *
 *----------------------------------------------------------------------
 */

page_handle *
clockcache_alloc(clockcache *cc, uint64 addr, page_type type)
{
  auto t = CacheOpsNamespace::alloc(cc->ic->ct, get_local_state(cc), clockcache_divide_by_page_size(cc, addr));
  bool success = t.get<0>();
  PHType ph = t.get<1>();
  if (!success) {
    fail("alloc failed");
  }
  return to_page_handle_pointer(cc, ph);
}

/*
 *----------------------------------------------------------------------
 *
 * clockcache_try_dealloc_page --
 *
 *      Evicts the page with address addr if it is in cache.
 *
 *----------------------------------------------------------------------
 */

void
clockcache_try_dealloc_page(clockcache *cc,
                            uint64      addr)
{
  CacheOpsNamespace::try__dealloc__page(cc->ic->ct, get_local_state(cc), clockcache_divide_by_page_size(cc, addr));
}

/*
 *----------------------------------------------------------------------
 *
 * clockcache_dealloc --
 *
 *      Lowers the allocator ref count on the extent with the given base
 *      address. If the ref count logically drops to 0 (1 in the allocator),
 *      any of those pages which are in cache are also freed and then the
 *      allocation is release (the allocator ref count is lowered to 0).
 *      If this drops to 0, the block is freed.
 *
 *----------------------------------------------------------------------
 */

uint32_t
clockcache_dealloc(clockcache *cc,
                   uint64      addr,
                   page_type   type)
{
   debug_assert(addr % cc->cfg->extent_size == 0);
   //const threadid tid = platform_get_tid();

   clockcache_log(addr, 0, "dealloc extent: addr %lu\n", addr);
   uint8 allocator_rc = allocator_dec_refcount(cc->al, addr);
   if (allocator_rc == 2) {
      // this means it is now 1, meaning not free but unref'd
      for (uint64 i = 0; i < cc->cfg->pages_per_extent; i++) {
         uint64 page_addr = addr + clockcache_multiply_by_page_size(cc, i);
         clockcache_try_dealloc_page(cc, page_addr);
      }
      allocator_rc = allocator_dec_refcount(cc->al, addr);
      debug_assert(allocator_rc == 1);
      //if (cc->cfg->use_stats) {
      //   cc->stats[tid].page_deallocs[type] += cc->cfg->pages_per_extent;
      //}
      return TRUE;
   }
   return FALSE;
}

/*
 *----------------------------------------------------------------------
 *
 * clockcache_get_allocator_ref --
 *
 *      Returns the allocator ref count of the addr.
 *
 *----------------------------------------------------------------------
 */

uint8
clockcache_get_allocator_ref(clockcache *cc, uint64 addr)
{
   return allocator_get_refcount(cc->al, addr);
}

/*
 *----------------------------------------------------------------------
 *
 * clockcache_get --
 *
 *      Returns a pointer to the page_handle for the page with address addr.
 *      Calls clockcachge_get_int till a retry is needed.
 *
 *      If blocking is set, then it blocks until the page is unlocked as well.
 *
 *      Returns with a read lock held.
 *
 *----------------------------------------------------------------------
 */

page_handle *
clockcache_get(clockcache *cc,
               uint64     addr,
               uint32_t       blocking,
               page_type  type)
{
  if (!blocking) {
    fail("clockcache_get non blocking");
  }
  PHType ph = CacheOpsNamespace::get(cc->ic->ct, get_local_state(cc), clockcache_divide_by_page_size(cc, addr));
  return to_page_handle_pointer(cc, ph);
}

/*
 *----------------------------------------------------------------------
 *
 * clockcache_get_async --
 *
 *      Async version of clockcache_get(). This can return one of the
 *      following:
 *      - async_locked : page is write locked or being loaded
 *      - async_no_reqs : ran out of async requests (queue depth of device)
 *      - async_success : page hit in the cache. callback won't be called. Read
 *        lock is held on the page on return.
 *      - async_io_started : page miss in the cache. callback will be called
 *        when it's loaded. Page read lock is held after callback is called.
 *        The callback is not called on a thread context. It's the user's
 *        responsibility to call cache_async_done() on the thread context
 *        after the callback is done.
 *
 *----------------------------------------------------------------------
 */

cache_async_result
clockcache_get_async(clockcache        *cc,        // IN
                     uint64             addr,      // IN
                     page_type          type,      // IN
                     cache_async_ctxt  *ctxt)      // IN
{
  fail("get_async");
}


/*
 *----------------------------------------------------------------------
 *
 * clockcache_async_done --
 *
 *    Called from thread context after the async callback has been invoked.
 *    Currently, it just updates cache miss stats.
 *
 *----------------------------------------------------------------------
 */
void
clockcache_async_done(clockcache       *cc,
                      page_type         type,
                      cache_async_ctxt *ctxt)
{
  fail("async_done");
}


void
clockcache_unget(clockcache *cc,
                 page_handle *page)
{
  CacheOpsNamespace::unget(cc->ic->ct, get_local_state(cc), page_handle_index(cc, page));
}


/*
 *----------------------------------------------------------------------
 *
 * clockcache_claim --
 *
 *      Upgrades a read lock to a claim. This function does not block and
 *      returns TRUE if the claim was successfully obtained.
 *
 *      A claimed node has the CC_CLAIMED bit set in its status vector.
 *
 *      NOTE: When a call to claim fails, the caller must drop and reobtain the
 *      readlock before trying to claim again to avoid deadlock.
 *
 *----------------------------------------------------------------------
 */

uint32_t
clockcache_claim(clockcache *cc,
                 page_handle *page)
{
  bool b = CacheOpsNamespace::claim(cc->ic->ct, page_handle_index(cc, page));
  //const threadid tid = platform_get_tid();
  //std::cout << "thread " << tid << " claim" << "(" << page_handle_index(cc, page).cache__idx << ")"
  //    << ") " << (b ? 1 : 0) << std::endl;
  //printf("c++ b = %d %d\n", (int)b, (int)sizeof(bool));
  return (uint32_t)b;
}

void
clockcache_unclaim(clockcache *cc,
                   page_handle *page)
{
  CacheOpsNamespace::unclaim(cc->ic->ct, page_handle_index(cc, page));
  //const threadid tid = platform_get_tid();
  //std::cout << "thread " << tid << " unclaim" << "(" << page_handle_index(cc, page).cache__idx << ")"
  //    << ") " << std::endl;
}


/*
 *----------------------------------------------------------------------
 *
 * clockcache_lock --
 *
 *     Write locks a claimed page and blocks while any read locks are released.
 *
 *     The write lock is indicated by having the CC_WRITELOCKED flag set in
 *     addition to the CC_CLAIMED flag.
 *
 *----------------------------------------------------------------------
 */

void
clockcache_lock(clockcache  *cc,
                page_handle *page)
{
  //const threadid tid = platform_get_tid();
  //std::cout << "thread " << tid << " lock" << "(" << page_handle_index(cc, page).cache__idx << ")" << std::endl;
  return CacheOpsNamespace::lock(cc->ic->ct, get_local_state(cc), page_handle_index(cc, page));
}

void
clockcache_unlock(clockcache  *cc,
                  page_handle *page)
{
  CacheOpsNamespace::unlock(cc->ic->ct, page_handle_index(cc, page));
}


/*----------------------------------------------------------------------
 *
 * clockcache_mark_dirty --
 *
 *      Marks the entry dirty.
 *
 *      FIXME: [aconway 2020-03-23]
 *      Maybe this should just get rolled into clockcache_lock?
 *
 *----------------------------------------------------------------------
 */

void
clockcache_mark_dirty(clockcache *cc,
                      page_handle *page)
{
  CacheOpsNamespace::mark__dirty(cc->ic->ct, page_handle_index(cc, page));
}

/*
 *----------------------------------------------------------------------
 *
 * clockcache_pin --
 *
 *      Functionally equivalent to an anonymous read lock. Implemented using a
 *      special ref count.
 *
 *      A write lock must be held while pinning to avoid a race with eviction.
 *
 *----------------------------------------------------------------------
 */

void
clockcache_pin(clockcache *cc,
               page_handle *page)
{
  fail("pin");
}

void
clockcache_unpin(clockcache *cc,
                 page_handle *page)
{
  fail("unpin");
}

/*
 *-----------------------------------------------------------------------------
 *
 * clockcache_page_sync --
 *
 *      Asynchronously syncs the page. Currently there is no way to check when
 *      the writeback has completed.
 *
 *-----------------------------------------------------------------------------
 */

void
clockcache_page_sync(clockcache  *cc,
                     page_handle *page,
                     uint32_t         is_blocking,
                     page_type    type)
{
  if (is_blocking) {
    CacheOpsNamespace::page__sync__blocking(
        cc->ic->ct, get_local_state(cc), page_handle_index(cc, page));
  } else {
    CacheOpsNamespace::page__sync__nonblocking(
        cc->ic->ct, get_local_state(cc), page_handle_index(cc, page));
  }
}


/*
 *----------------------------------------------------------------------
 *
 * clockcache_sync_callback --
 *
 *      internal callback for clockcache_extent_sync which decrements the pages
 *      outstanding counter
 *
 *----------------------------------------------------------------------
 */

/*
 *-----------------------------------------------------------------------------
 *
 * clockcache_extent_sync --
 *
 *      Asynchronously syncs the extent.
 *
 *      Adds the number of pages issued writeback to the coutner pointered to
 *      by pages_outstanding. When the writes complete, a callback subtracts
 *      them off, so that the caller may track how many pages are in writeback.
 *
 *      Assumes all pages in the extent are clean or cleanable
 *
 *-----------------------------------------------------------------------------
 */

void
clockcache_extent_sync(clockcache *cc,
                       uint64      addr,
                       uint64     *pages_outstanding)
{
  fail("extent_sync");
}

/*
 *-----------------------------------------------------------------------------
 *
 * clockcache_prefetch --
 *
 *      prefetch asynchronously loads the extent with given base address
 *
 *-----------------------------------------------------------------------------
 */


void
clockcache_prefetch(clockcache *cc, uint64 base_addr, page_type type)
{
  CacheOpsNamespace::prefetch(
        cc->ic->ct, get_local_state(cc),
        clockcache_divide_by_page_size(cc, base_addr));
}

/*
 *----------------------------------------------------------------------
 *
 * clockcache_print --
 *
 *      Prints a bitmap representation of the cache.
 *
 *----------------------------------------------------------------------
 */

void
clockcache_print(clockcache *cc)
{
  fail("clockcache_print");
}

uint32_t
clockcache_page_valid(clockcache *cc,
                      uint64      addr)
{
   if (addr % cc->cfg->page_size != 0)
      return FALSE;
   uint64 base_addr = addr - addr % cc->cfg->extent_size;
   if (addr < allocator_get_capacity(cc->al))
      return base_addr != 0 && allocator_get_refcount(cc->al, base_addr) != 0;
   else
      return FALSE;
}

void
clockcache_validate_page(clockcache  *cc,
                         page_handle *page,
                         uint64       addr)
{
   debug_assert(clockcache_page_valid(cc, addr));
   debug_assert(page->disk_addr == addr);
   //debug_assert(!clockcache_test_flag(cc, clockcache_page_to_entry_number(cc, page), CC_FREE));
   //debug_assert(
   //   (*cc->ic->ct.status__idx__array)[page_handle_index(cc, page).cache__idx].a.status.slot.load()
   //     != AtomicStatusImpl_Compile::flag__unmapped());
}

void
clockcache_assert_ungot(clockcache *cc,
                        uint64      addr)
{
  fail("assert_ungot");
}

void
clockcache_assert_noleaks(clockcache *cc)
{
  fail("assert_noleaks");
}

void
clockcache_io_stats(clockcache *cc,
                    uint64     *read_bytes,
                    uint64     *write_bytes)
{
  std::cout << "io_stats: not printing any stats" << std::endl;
}

void
clockcache_print_stats(clockcache *cc)
{
  std::cout << "print_stats: not printing any stats" << std::endl;
}

void
clockcache_reset_stats(clockcache *cc)
{
  std::cout << "reset_stats: not reseting any stats" << std::endl;
}

/*
 *----------------------------------------------------------------------
 *
 * verification functions for cache_test
 *
 *----------------------------------------------------------------------
 */

uint32
clockcache_count_dirty(clockcache *cc)
{
  fail("count_dirty");
}

uint16
clockcache_get_read_ref(clockcache *cc, page_handle *page)
{
  fail("get_read_ref");
}

uint32_t
clockcache_present(clockcache *cc, page_handle *page)
{
  fail("present");
}

static void
clockcache_enable_sync_get(clockcache *cc, uint32_t enabled)
{
  fail("enable_sync_get");
}

allocator *
clockcache_allocator(clockcache *cc)
{
   return cc->al;
}

void
clockcache_wait(clockcache *cc)
{
  CacheOpsNamespace::wait(cc->ic->ct);
}

void
clockcache_assert_no_refs_and_pins(clockcache *cc)
{
   uint32   i;
   uint32   j;
   for (i = 0; i < CC_RC_WIDTH; i++) {
      for (j = 0; j < cc->cfg->page_capacity; j++) {
         platform_assert(
           cc->ic->ct.read__refcount__atomic(i, j)->a.slot.load() == 0);
      }
   }
}

void
clockcache_assert_no_locks_held(clockcache *cc)
{
  uint64 i;
  clockcache_assert_no_refs_and_pins(cc);
  for (i = 0; i < cc->cfg->page_capacity; i++) {
    //debug_assert(!(
    //    (*cc->ic->ct.status__idx__array)[i].status.atomic.slot.load()
    //    & AtomicStatusImpl_Compile::flag__exc()));
  }
}

uint64
clockcache_get_page_size(const clockcache *cc)
{
   return cc->cfg->page_size;
}

uint64
clockcache_get_extent_size(const clockcache *cc)
{
   return cc->cfg->extent_size;
}
