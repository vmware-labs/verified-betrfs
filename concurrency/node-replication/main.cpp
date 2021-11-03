#include <cinttypes>
#include <optional>
#include <iostream>
#include <chrono>
#include <vector>

#include <thread>
#include <mutex>
#include <condition_variable>

#include "nr.h"

using duration = std::chrono::duration<uint64_t>;

struct benchmark_state {
  size_t n_threads;
  duration run_duration;
  std::atomic<size_t> n_threads_ready;
  std::atomic<bool> start_benchmark;
  std::atomic<bool> exit_benchmark;
  std::atomic<uint64_t> total_updates;
  std::atomic<uint64_t> total_reads;

  benchmark_state(size_t n_threads, duration run_duration)
    : n_threads{n_threads}
    , run_duration{run_duration}
    , n_threads_ready{}
    , start_benchmark{}
    , exit_benchmark{}
    , total_updates{}
    , total_reads{}
  {
  }
};

// - RwLock Benchmarking -

// Give a friendlier name to Dafny's generated namespace.
namespace rwlock = RwLockImpl_ON_Uint64ContentsTypeMod__Compile;
typedef rwlock::RwLock RwLockUint64;

void run_rwlock_bench(
    benchmark_state& state,
    uint8_t thread_id,
    RwLockUint64& rwlock)
{
  state.n_threads_ready++;
  while (!state.start_benchmark) {}

  uint64_t updates = 0;
  uint64_t reads = 0;
  while (!state.exit_benchmark.load(std::memory_order_relaxed)) {
    if ((reads + updates) & 0xf) { // do a read
      auto shared_guard = rwlock.acquire__shared(thread_id);
      uint64_t* value = rwlock::__default::borrow__shared(rwlock, shared_guard);
      rwlock.release__shared(shared_guard);
      ++reads;
    } else { // do a write
      bool value = rwlock.acquire();
      rwlock.release(value + 1);
      ++updates;
    }
  }

  state.total_updates += updates;
  state.total_reads += reads;
}

void bench_rwlock(benchmark_state& state) {
  auto rwlock = rwlock::__default::new__mutex(false);

  std::vector<std::thread> threads{};
  for (uint8_t thread_id = 0; thread_id < state.n_threads; ++thread_id)
    threads.emplace_back(std::thread{run_rwlock_bench,
                                     std::ref(state),
                                     thread_id,
                                     std::ref(rwlock)});

  while (state.n_threads_ready < state.n_threads);
  state.start_benchmark = true;
  std::this_thread::sleep_for(state.run_duration);
  state.exit_benchmark = true;

  for (auto& thread : threads)
    thread.join();

  std::cout << std::endl
            << "threads " << state.n_threads << std::endl
            << "updates " << state.total_updates << std::endl
            << "reads   " << state.total_reads << std::endl;
}

// - NR-related stuff -

void run_nr_bench(
    benchmark_state& state,
    uint8_t thread_id,
    nr_helper& nr_helper)
{
  // TODO(stutsman): pin threads properly

  nr::ThreadOwnedContext* context = nr_helper.register_thread(thread_id);

  state.n_threads_ready++;
  while (!state.start_benchmark) {}

  // Run one initial read to make sure the count is correct.
  Tuple<uint64_t, nr::ThreadOwnedContext> r =
    Impl_ON_CounterIfc__Compile::__default::do__read(
      nr_helper.get_nr(),
      nr_helper.get_node(thread_id),
      CounterIfc_Compile::ReadonlyOp{},
      *context);
    std::cout << "thread_id final nr initial value: " << r.get<0>() << std::endl;

  uint64_t reads = 0;
  uint64_t updates = 0;
  while (!state.exit_benchmark.load(std::memory_order_relaxed)) {
    if ((reads + updates) & 0xf) { // do a read
      Tuple<uint64_t, nr::ThreadOwnedContext> r =
        Impl_ON_CounterIfc__Compile::__default::do__read(
          nr_helper.get_nr(),
          nr_helper.get_node(thread_id),
          CounterIfc_Compile::ReadonlyOp{},
          *context);
      ++reads;
    } else { // do a write
      Tuple<uint64_t, nr::ThreadOwnedContext> r =
        Impl_ON_CounterIfc__Compile::__default::do__update(
          nr_helper.get_nr(),
          nr_helper.get_node(thread_id),
          CounterIfc_Compile::UpdateOp{},
          *context);
      ++updates;
    }
  }

  // Run one last read to make sure the final count is correct.
  r =
    Impl_ON_CounterIfc__Compile::__default::do__read(
      nr_helper.get_nr(),
      nr_helper.get_node(thread_id),
      CounterIfc_Compile::ReadonlyOp{},
      *context);
    std::cout << "thread_id final nr counter value: " << r.get<0>() << std::endl;

  state.total_updates += updates;
  state.total_reads += reads;
}

void bench_nr(benchmark_state& state)
{
  nr_helper nr_helper{};
  nr_helper.init_nr();

  std::vector<std::thread> threads{};
  for (uint8_t thread_id = 0; thread_id < state.n_threads; ++thread_id) {
    threads.emplace_back(std::thread{run_nr_bench,
                                     std::ref(state),
                                     thread_id,
                                     std::ref(nr_helper)});
  }

  while (state.n_threads_ready < state.n_threads);
  state.start_benchmark = true;
  std::this_thread::sleep_for(state.run_duration);
  state.exit_benchmark = true;

  for (auto& thread : threads)
    thread.join();

  std::cout << std::endl
            << "threads " << state.n_threads << std::endl
            << "updates " << state.total_updates << std::endl
            << "reads   " << state.total_reads << std::endl;
}

int main(int argc, char* argv[]) {
  const auto run_duration = std::chrono::seconds{1};

  if (argc < 2) {
    std::cerr << "usage: " << argv[0] << " <rwlock|nr>" << std::endl;
    exit(-1);
  }

  std::string bench = std::string{argv[1]};

  benchmark_state state{NUM_THREADS, run_duration};
  if (bench == "rwlock") {
    bench_rwlock(state);
  } else {
    bench_nr(state);
  }

  return 0;
}
