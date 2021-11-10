#include <cinttypes>
#include <optional>
#include <iostream>
#include <chrono>
#include <vector>
#include <string>
#include <fstream>

#include <thread>
#include <mutex>
#include <shared_mutex>
#include <condition_variable>
#include "vspace_glue.h"
#include "nr.h"
#include "thread_pin.h"

class KeyGenerator {
  uint64_t state;

  // key range is: `VSPACE_RANGE` as defined in vspace/lib.rs
  // adjust this number together with `MASK` (= VSPACE_RANGE & !0xfff):
  static constexpr uint64_t MASK = 0x3fffffffff & !0xfff;

public:
  KeyGenerator(uint8_t thread_id)
    : state{0xdeadbeefdeadbeef ^ thread_id}
  {}

  // https://en.wikipedia.org/wiki/Xorshift
  uint64_t next() {
    uint64_t x = state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    state = x;
    return x & MASK;
  }
};

using seconds = std::chrono::seconds;

struct benchmark_state {
  std::string bench_name;
  size_t n_threads;
  size_t reads_pct;
  size_t reads_stride;
  size_t updates_stride;
  seconds run_seconds;
  core_map cores;
  std::atomic<size_t> n_threads_ready;
  std::vector<std::thread> threads;
  std::atomic<bool> start_benchmark;
  std::atomic<bool> exit_benchmark;
  std::atomic<size_t> n_threads_finished;
  std::atomic<uint64_t> total_updates;
  std::atomic<uint64_t> total_reads;

  static constexpr size_t stride1 = 10000;

  benchmark_state(std::string& bench_name,
                  size_t n_threads,
                  size_t reads_pct,
                  seconds run_seconds,
                  core_map::numa_policy numa_policy,
                  core_map::core_policy core_policy)
    : bench_name{bench_name}
    , n_threads{n_threads}
    , reads_pct{reads_pct}
    , reads_stride{reads_pct != 0 ? stride1 * 100 / reads_pct : ~0lu}
    , updates_stride{reads_pct == 100 ? ~0lu: stride1 * 100 / (100 - reads_pct)}
    , run_seconds{run_seconds}
    , cores{numa_policy, core_policy}
    , n_threads_ready{}
    , threads{}
    , start_benchmark{}
    , exit_benchmark{}
    , n_threads_finished{}
    , total_updates{}
    , total_reads{}
  {}

  void dump_json() {
    std::string outpath{"data-"};
    outpath += bench_name + "-";
    outpath += std::to_string(n_threads) + "-";
    outpath += std::to_string(reads_pct) + "-";
    outpath += std::to_string(nr_helper::num_replicas()) + "-";
    outpath += std::to_string(run_seconds.count()) + "-";
    outpath += cores.get_numa_policy() == core_map::NUMA_INTERLEAVE ?
                    "interleave" : "fill";
    outpath += ".json";
    std::ofstream out{outpath.c_str()};

    out << "{" << std::endl
        << "  \"bench_name\": \"" << bench_name << "\"," << std::endl
        << "  \"n_threads\": " << n_threads << "," << std::endl
        << "  \"reads_pct\": " << reads_pct << "," << std::endl
        << "  \"n_replicas\": " << nr_helper::num_replicas() << "," << std::endl
        << "  \"run_seconds\": " << run_seconds.count() << "," << std::endl
        << "  \"numa_policy\": " << cores.get_numa_policy() << "," << std::endl
        << "  \"core_policy\": " << cores.get_core_policy() << "," << std::endl
        << "  \"reads\": " << total_reads << "," << std::endl
        << "  \"updates\": " << total_updates << "," << std::endl
        << "  \"total_ops\": " << total_reads + total_updates << "," << std::endl
        << "  \"reads_per_s\": "
          << static_cast<double>(total_reads) / run_seconds.count()
          << "," << std::endl
        << "  \"updates_per_s\": "
          << static_cast<double>(total_updates) / run_seconds.count()
          << "," << std::endl
        << "  \"ops_per_s\": "
          << static_cast<double>(total_reads + total_updates) / run_seconds.count()
          << "," << std::endl
        << "}" << std::endl;
  }
};

template <typename Monitor>
void run_thread(
    uint8_t thread_id,
    benchmark_state& state,
    Monitor& monitor)
{
  state.cores.pin(thread_id);

  KeyGenerator keygen{thread_id};
  void* thread_context = monitor.create_thread_context(thread_id);

  state.n_threads_ready++;
  while (!state.start_benchmark) {}

  uint64_t updates = 0;
  uint64_t reads = 0;
  uint64_t updates_vruntime = 0;
  uint64_t reads_vruntime = 0;
  while (!state.exit_benchmark.load(std::memory_order_relaxed)) {
    uint64_t key = keygen.next();
    uint64_t val = keygen.next();
    if (reads_vruntime <= updates_vruntime) {
      monitor.read(thread_id, thread_context, key);
      ++reads;
      reads_vruntime += state.reads_stride;
    } else { // do an update
      monitor.update(thread_id, thread_context, key, val);
      ++updates;
      updates_vruntime += state.updates_stride;
    }
  }

  state.n_threads_finished++;
  while (state.n_threads_finished < state.n_threads)
    monitor.finish_up(thread_id, thread_context);

  state.total_updates += updates;
  state.total_reads += reads;
}

// - C++ shared_mutex Benchmarking -

struct cpp_shared_mutex_monitor {
  using s_lock = std::shared_lock<std::shared_mutex>;
  using x_lock = std::unique_lock<std::shared_mutex>;

  std::shared_mutex mutex;
#if USE_COUNTER
  uint64_t value;
#else
  ::VSpacePtr vspace;
#endif

  cpp_shared_mutex_monitor(size_t n_threads)
    : mutex{}
#if USE_COUNTER
    , value{}
#else
    , vspace{createVSpace()}
#endif
  {}

  ~cpp_shared_mutex_monitor() {
  #if USE_COUNTER
  #else
    //delete vspace; // TODO(stutsman): ~VSpace is deleted for some reason?
  #endif
  }

  void* create_thread_context(uint8_t thread_id) { return nullptr; }

  uint64_t read(uint8_t thread_id, void* thread_context, uint64_t key) {
  #if USE_COUNTER
    s_lock lock{mutex};
    return value;
  #else
    s_lock lock{mutex};
    return vspace->resolveWrapped(key);
  #endif
  }

  void update(uint8_t thread_id, void* thread_context, uint64_t key, uint64_t value) {
  #if USE_COUNTER
    x_lock lock{mutex};
    ++value;
  #else
    x_lock lock{mutex};
    vspace->mapGenericWrapped(key, key, 4096);
  #endif
  }

  void finish_up(uint8_t thread_id, void* thread_context) {}

  static void run_thread(
      uint8_t thread_id,
      benchmark_state& state,
      cpp_shared_mutex_monitor& monitor)
  {
    ::run_thread(thread_id, state, monitor);
  }
};

// - RwLock Benchmarking -

// Give a friendlier name to Dafny's generated namespace.
#if USE_COUNTER
namespace rwlock = RwLockImpl_ON_Uint64ContentsTypeMod__Compile;
#else
namespace rwlock = RwLockImpl_ON_VSpaceContentsTypeMod__Compile;
#endif
typedef rwlock::RwLock RwLockT;

struct dafny_rwlock_monitor {
  RwLockT lock;

  dafny_rwlock_monitor(size_t n_threads)
  #if USE_COUNTER
    : lock{rwlock::__default::new__mutex(0lu)}
  #else
    : lock{rwlock::__default::new__mutex(createVSpace())}
  #endif
  {}

  ~dafny_rwlock_monitor() {
  #if USE_COUNTER
  #else
    ::VSpacePtr vspace = lock.acquire();
    // delete vspace; // TODO(stutsman): ~VSpace is deleted for some reason?
    lock.release(nullptr);
  #endif
  }

  void* create_thread_context(uint8_t thread_id) {
    return nullptr;
  }

  uint64_t read(uint8_t thread_id, void* thread_context, uint64_t key) {
  #if USE_COUNTER
    auto shared_guard = lock.acquire__shared(thread_id);
    uint64_t value = *rwlock::__default::borrow__shared(lock, shared_guard);
    lock.release__shared(shared_guard);
    return value;
  #else
    auto shared_guard = lock.acquire__shared(thread_id);
    ::VSpacePtr vspace = *rwlock::__default::borrow__shared(lock, shared_guard);
    uint64_t value = vspace->resolveWrapped(key);
    lock.release__shared(shared_guard);
    return value;
  #endif
  }

  void update(uint8_t thread_id, void* thread_context, uint64_t key, uint64_t value) {
#if USE_COUNTER
    uint64_t val = lock.acquire();
    lock.release(val + 1);
#else
    ::VSpacePtr vspace = lock.acquire();
    bool ok = vspace->mapGenericWrapped(key, value, 4096);
    lock.release(vspace);
#endif
  }

  void finish_up(uint8_t thread_id, void* thread_context) {}

  static void run_thread(
      uint8_t thread_id,
      benchmark_state& state,
      dafny_rwlock_monitor& monitor)
  {
    ::run_thread(thread_id, state, monitor);
  }
};

// - NR Benchmarking -

struct dafny_nr_monitor{
  nr_helper helper;

  dafny_nr_monitor(size_t n_threads)
    : helper{n_threads}
  {
    helper.init_nr();
  }

  void* create_thread_context(uint8_t thread_id) {
    return helper.register_thread(thread_id);
  }

  uint64_t read(uint8_t thread_id, void* context, uint64_t key) {
    auto c = static_cast<nr::ThreadOwnedContext*>(context);
#if USE_COUNTER
    auto op = CounterIfc_Compile::ReadonlyOp{}; 
#else
    auto op = VSpaceIfc_Compile::ReadonlyOp{key}; 
#endif
    Tuple<uint64_t, nr::ThreadOwnedContext> r =
      nr::__default::do__read(
        helper.get_nr(),
        helper.get_node(thread_id),
        op,
        *c);

    return r.get<0>();
  }

  void update(uint8_t thread_id, void* context, uint64_t key, uint64_t value) {
    auto c = static_cast<nr::ThreadOwnedContext*>(context);
#if USE_COUNTER
    auto op = CounterIfc_Compile::UpdateOp{}; 
#else
    auto op = VSpaceIfc_Compile::UpdateOp{key, value}; 
#endif
    nr::__default::do__update(
      helper.get_nr(),
      helper.get_node(thread_id),
      op,
      *c);
  }

  void finish_up(uint8_t thread_id, void* context) {
    auto c = static_cast<nr::ThreadOwnedContext*>(context);
    nr::__default::try__combine(
      helper.get_nr(),
      helper.get_node(thread_id),
      c->tid);
  }

  static void run_thread(
      uint8_t thread_id,
      benchmark_state& state,
      dafny_nr_monitor& monitor)
  {
    ::run_thread(thread_id, state, monitor);
  }
};

// - Rust NR Benchmarking -

struct rust_nr_monitor{
  nr_rust_helper helper;

  rust_nr_monitor(size_t n_threads)
    : helper{n_threads}
  {
    helper.init_nr();
  }

  void* create_thread_context(uint8_t thread_id) {
    return (void*)helper.register_thread(thread_id);
  }

  uint64_t read(uint8_t thread_id, void* context, uint64_t key) {
    size_t replica_token = (size_t) context;
#if USE_COUNTER
    #error "NYI"
#else
    helper.get_node(thread_id)->ReplicaResolve(replica_token, key);
#endif
    return 0;
  }

  void update(uint8_t thread_id, void* context, uint64_t key, uint64_t value) {
    size_t replica_token = (size_t)context;
#if USE_COUNTER
  #error "NYI"
#else
    bool ok = helper.get_node(thread_id)->ReplicaMap(replica_token, key, value);
#endif
  }

  void finish_up(uint8_t thread_id, void* context) {
    auto replica_token = (size_t)context;
    helper.get_node(thread_id)->ReplicaResolve(replica_token, 0x0);
  }

  static void run_thread(
      uint8_t thread_id,
      benchmark_state& state,
      rust_nr_monitor& monitor)
  {
    ::run_thread(thread_id, state, monitor);
  }
};

template <typename Monitor>
void bench(benchmark_state& state, Monitor& monitor)
{
  for (uint8_t thread_id = 0; thread_id < state.n_threads; ++thread_id) {
    state.threads.emplace_back(std::thread{Monitor::run_thread,
                                           thread_id,
                                           std::ref(state),
                                           std::ref(monitor)});
  }

  while (state.n_threads_ready < state.n_threads);
  state.start_benchmark = true;
  std::this_thread::sleep_for(state.run_seconds);
  state.exit_benchmark = true;

  for (auto& thread : state.threads)
    thread.join();

  std::cerr << std::endl
            << "threads " << state.n_threads << std::endl
            << "updates " << state.total_updates << std::endl
            << "reads   " << state.total_reads << std::endl;

  state.dump_json();
}

void usage(const char* argv0) {
  std::cerr << "usage: " << argv0
            << " <benchmarkname> <n_threads> <read_pct>"
            << " <n_seconds> <fill|interleave>"
            << std::endl;
  exit(-1);
}

int main(int argc, char* argv[]) {
  if (argc < 6)
    usage(argv[0]);

  //LogWrapper& lw = createLog();
  //ReplicaWrapper* rw = createReplica(lw);
  //auto tkn = rw->RegisterWrapper();
  //rw->ReplicaMap(tkn, 0x2000, 0x3000);
  //rw->ReplicaResolve(tkn, 0x2000);

  //VSpace* vspace = createVSpace();
  //vspace->mapGenericWrapped(0x2000, 0x3000, 0x1000);

  std::string bench_name = std::string{argv[1]};

  const size_t n_threads = atoi(argv[2]);
  assert(n_threads > 0);

  const size_t reads_pct = atoi(argv[3]);
  assert(reads_pct <= 100);

  const size_t n_seconds = atoi(argv[4]);
  assert(n_seconds > 0);
  const auto run_seconds = std::chrono::seconds{n_seconds};

  core_map::numa_policy fill_policy;
  const std::string policy_name = std::string{argv[5]};
  if (policy_name == "fill") {
    fill_policy = core_map::NUMA_FILL;
  } else if (policy_name == "interleave") {
    fill_policy = core_map::NUMA_INTERLEAVE;
  } else {
    usage(argv[0]);
  }

  disable_dvfs();

  benchmark_state state{
    bench_name,
    n_threads,
    reads_pct,
    run_seconds,
    fill_policy,
    core_map::core_policy::CORES_FILL
  };

#define BENCHMARK(test_name) \
  if (bench_name == #test_name) { \
    test_name ## _monitor monitor{n_threads}; \
    bench(state, monitor); \
    exit(0); \
  }

  BENCHMARK(cpp_shared_mutex);
  BENCHMARK(dafny_rwlock);
  BENCHMARK(dafny_nr);
  BENCHMARK(rust_nr);

  std::cerr << "unrecognized benchmark name " << bench_name << std::endl;

  return -1;
}
