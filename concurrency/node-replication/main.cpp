#include "DafnyRuntime.h"

// Include Extern.h before generated Bundle.i.h.
// Bundle.i.h depends on it but it can't include it itself.
#include "Extern.h"
#include "LinearExtern.h"
#include "Bundle.i.h"

#include "nrconstants.h"

#include <cinttypes>
#include <optional>
#include <iostream>
#include <chrono>
#include <vector>

#include <thread>
#include <mutex>
#include <condition_variable>

#include <memory>

// - RwLock Benchmarking -

// Give a friendlier name to Dafny's generated namespace.
namespace rwlock = RwLockImpl_ON_BoolContentsTypeMod__Compile;
typedef rwlock::RwLock RwLockBool;

std::atomic<size_t> n_threads_ready{0};
std::atomic<bool> start_benchmark{false};
std::atomic<bool> exit_benchmark{false};

void run_rwlock_bench(
    uint8_t thread_id,
    RwLockBool& rwlock,
    std::atomic<uint64_t>& total_iters)
{
  n_threads_ready++;
  while (!start_benchmark) {}

  uint64_t iters = 0;
  while (!exit_benchmark.load(std::memory_order_relaxed)) {
    if (iters & ~0xf) { // do a read
      auto shared_guard = rwlock.acquire__shared(thread_id);
      bool* value = rwlock::__default::borrow__shared(rwlock, shared_guard);
      rwlock.release__shared(shared_guard);
    } else { // do a write
      bool value = rwlock.acquire();
      value = !value;
      rwlock.release(value);
    }

    ++iters;
  }

  total_iters += iters;
}

template <typename Duration>
void bench_rwlock(size_t n_threads, Duration run_duration) {
  auto rwlock = rwlock::__default::new__mutex(false);
  std::atomic<uint64_t> total_iters{0};

  std::vector<std::thread> threads{};
  for (uint8_t thread_id = 0; thread_id < n_threads; ++thread_id)
    threads.emplace_back(std::thread{run_rwlock_bench,
                                     thread_id,
                                     std::ref(rwlock),
                                     std::ref(total_iters)});

  while (n_threads_ready < n_threads);
  start_benchmark = true;
  std::this_thread::sleep_for(run_duration);
  exit_benchmark = true;

  for (auto& thread : threads)
    thread.join();

  std::cout << n_threads << " threads iterated "
            << total_iters << " times" << std::endl;
}

template <typename Duration>
void bench_nr(size_t n_threads, Duration duration);

int main(int argc, char* argv[]) {
  const auto run_duration = std::chrono::seconds{1};

  if (argc < 2) {
    std::cerr << "usage: " << argv[0] << " <rwlock|nr>" << std::endl;
    exit(-1);
  }

  if (std::string{argv[1]} == "rwlock") {
    bench_rwlock(NUM_THREADS, run_duration);
  } else {
    bench_nr(NUM_THREADS, run_duration);
  }

  return 0;
}

// - NR-related stuff -

using LinearExtern::lseq;
namespace nr = Impl_ON_CounterIfc__Compile;
namespace nrinit = Init_ON_CounterIfc__Compile;

class nr_helper {
  std::optional<nr::NR> nr;
  std::mutex init_mutex;
  lseq<nrinit::NodeCreationToken> node_creation_tokens;
  std::unordered_map<uint8_t, nr::Node> nodes;
  /// Maps NodeId to vector of ThreadOwnedContexts for that Node.
  std::unordered_map<uint8_t, lseq<nr::ThreadOwnedContext>> thread_owned_contexts;
  std::condition_variable all_nodes_init;

 public:
  nr_helper()
    : nr{}
    , init_mutex{}
    , node_creation_tokens{}
    , nodes{}
    , thread_owned_contexts{}
    , all_nodes_init{}
  {}

  ~nr_helper() {
    for (auto seq : thread_owned_contexts)
      delete seq.second;

    delete node_creation_tokens;
  }

  nr::NR& get_nr() { return *nr; }

  nr::Node& get_node(uint8_t thread_id) {
    return nodes[thread_id / THREADS_PER_REPLICA];
  }

  void init_nr() {
    auto init = nrinit::__default::initNR();
    nr.emplace(init.get<0>());

    node_creation_tokens = init.get<1>();
    assert(node_creation_tokens->size() == 2);
  }

  nr::ThreadOwnedContext* register_thread(uint8_t thread_id) {
    std::unique_lock<std::mutex> lock{init_mutex};

    nrinit::NodeCreationToken* token{nullptr};
    if (thread_id % THREADS_PER_REPLICA == 0)
      token = &node_creation_tokens->at(thread_id / THREADS_PER_REPLICA).a;

    if (token) {
      auto r = nrinit::__default::initNode(*token);
      uint64_t node_id = r.get<0>().nodeId;
      std::cout << "thread_id " << static_cast<uint32_t>(thread_id)
                << " done initializing node_id " << node_id << std::endl;

      nodes.emplace(node_id, r.get<0>());
      thread_owned_contexts.emplace(node_id, r.get<1>());

      if (nodes.size() == NUM_REPLICAS) {
        for (const auto& pair : thread_owned_contexts) {
          const auto& contexts = pair.second;
          for (const auto& context : *contexts) {
            std::cout << "context tid " << context.a.tid << std::endl;
          }
        }
        all_nodes_init.notify_all();
      }
    }

    while (nodes.size() < NUM_REPLICAS)
      all_nodes_init.wait(lock);

    // TODO(stutsman) no pinning, affinity, and threads on different
    // nodes may actually use the wrong replica; all this needs to be
    // fixed if we want to use this harness.
    const uint8_t node_id = thread_id / THREADS_PER_REPLICA;
    const uint8_t context_index = thread_id % THREADS_PER_REPLICA;

    std::cout << "thread_id " << static_cast<uint32_t>(thread_id)
              << " registered with node_id " << static_cast<uint32_t>(node_id)
              << " context " << static_cast<uint32_t>(context_index)
              << std::endl;

    return &thread_owned_contexts.at(node_id)->at(context_index).a;
  }
};

void run_nr_bench(
    uint8_t thread_id,
    nr_helper& nr_helper,
    std::atomic<uint64_t>& total_iters)
{
  // TODO(stutsman): pin threads properly

  nr::ThreadOwnedContext* context = nr_helper.register_thread(thread_id);

  n_threads_ready++;
  while (!start_benchmark) {}

  uint64_t iters = 0;
  while (!exit_benchmark.load(std::memory_order_relaxed)) {
    if (iters & ~0xf) { // do a read
      std::cerr << "thread_id " << thread_id << "calling with tid " << context->tid << std::endl;
      Tuple<uint64_t, nr::ThreadOwnedContext> r =
        Impl_ON_CounterIfc__Compile::__default::do__read(
          nr_helper.get_nr(),
          nr_helper.get_node(thread_id),
          CounterIfc_Compile::ReadonlyOp{},
          *context);
          std::cerr << "read_op done" << std::endl;
    } else { // do a write
      std::cerr << "thread_id " << thread_id << "calling with tid " << context->tid << std::endl;
      Tuple<uint64_t, nr::ThreadOwnedContext> r =
        Impl_ON_CounterIfc__Compile::__default::do__update(
          nr_helper.get_nr(),
          nr_helper.get_node(thread_id),
          CounterIfc_Compile::UpdateOp{},
          *context);
          std::cerr << "update_op done" << std::endl;
    }

    ++iters;
  }

  total_iters += iters;
}

template <typename Duration>
void bench_nr(size_t n_threads, Duration run_duration) {
  nr_helper nr_helper{};
  nr_helper.init_nr();

  std::atomic<uint64_t> total_iters{0};
  std::vector<std::thread> threads{};
  for (uint8_t thread_id = 0; thread_id < n_threads; ++thread_id) {
    threads.emplace_back(std::thread{run_nr_bench,
                                     thread_id,
                                     std::ref(nr_helper),
                                     std::ref(total_iters)});
  }

  while (n_threads_ready < n_threads);
  start_benchmark = true;
  std::this_thread::sleep_for(run_duration);
  exit_benchmark = true;

  for (auto& thread : threads)
    thread.join();

  std::cout << n_threads << " threads iterated "
            << total_iters << " times" << std::endl;
}

