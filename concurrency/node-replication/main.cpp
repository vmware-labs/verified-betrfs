#include "DafnyRuntime.h"

// Include Extern.h before generated Bundle.i.h.
// Bundle.i.h depends on it but it can't include it itself.
#include "Extern.h"
#include "LinearExtern.h"
#include "Bundle.i.h"

#include <iostream>
#include <chrono>
#include <thread>
#include <vector>

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

int main(int argc, char* argv[]) {
  const size_t n_threads = 4;
  const auto run_duration = std::chrono::seconds{1};

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

  return 0;
}

// - NR-related stuff -

using LinearExtern::lseq;
using Impl_ON_CounterIfc__Compile::NR;
using Init_ON_CounterIfc__Compile::NodeCreationToken;

void initNR() {
  auto init = Init_ON_CounterIfc__Compile::__default::initNR();

  NR nr = init.get<0>();
  lseq<NodeCreationToken> tokens = init.get<1>();

  for (const auto& token : *tokens) {
  }
}

