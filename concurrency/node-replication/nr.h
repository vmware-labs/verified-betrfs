#ifndef NR_H
#define NR_H

#include "DafnyRuntime.h"

#include "Extern.h"
#include "LinearExtern.h"

#ifdef USE_COUNTER
#include "BundleCounter.i.h"
#else
#include "BundleVSpace.i.h"
#endif

#include <cinttypes>
#include <optional>
#include <iostream>
#include <chrono>
#include <vector>

#include <thread>
#include <mutex>
#include <condition_variable>

#include <memory>

using LinearExtern::lseq;

#ifdef USE_COUNTER
namespace nr = Impl_ON_CounterIfc__Compile;
namespace nrinit = Init_ON_CounterIfc__Compile;
#else
namespace nr = NRImpl_ON_VSpaceIfc__Compile;
namespace nrinit = Init_ON_VSpaceIfc__Compile;
#endif

class nr_helper {
  uint32_t n_threads_per_replica;
  std::optional<nr::NR> nr;
  std::mutex init_mutex;
  size_t nodes_init;
  lseq<nrinit::NodeCreationToken> node_creation_tokens;
  std::vector<std::unique_ptr<nr::Node>> nodes;
  /// Maps NodeId to vector of ThreadOwnedContexts for that Node.
  std::vector<lseq<nr::ThreadOwnedContext>> thread_owned_contexts;
  std::condition_variable all_nodes_init;

 public:
  static uint64_t num_replicas() {
    return NRConstants_Compile::__default::NUM__REPLICAS;
  }

  nr_helper(size_t n_threads)
    : n_threads_per_replica{static_cast<uint32_t>(n_threads / num_replicas())}
    , nr{}
    , init_mutex{}
    , nodes_init{}
    , node_creation_tokens{}
    , nodes{}
    , thread_owned_contexts{}
    , all_nodes_init{}
  {
    nodes.resize(num_replicas());
    thread_owned_contexts.resize(num_replicas());
    assert(num_replicas() > 0);
    assert(num_replicas() <= n_threads);
    assert(n_threads_per_replica * num_replicas() == n_threads);
  }

  nr::NR& get_nr() { return *nr; }

  static uint32_t get_node_id(uint32_t core_id) {
    return core_id % 2;
  }

  nr::Node* get_node(uint32_t core_id) {
    return nodes[get_node_id(core_id)].get();
  }

  void init_nr() {
    auto init = nrinit::__default::initNR();
    nr.emplace(init.get<0>());

    node_creation_tokens = init.get<1>();
    assert(node_creation_tokens.len == num_replicas());
  }

  nr::ThreadOwnedContext* register_thread(uint32_t core_id) {
    const uint32_t node_id = get_node_id(core_id);

    if (core_id / num_replicas() == 0) {
      auto token =
        &node_creation_tokens.ptr[node_id].a;
      auto r = nrinit::__default::initNode(*token);
      std::cerr << "thread on core_id " << core_id
                << " done initializing node_id "
                << node_id << std::endl;

      nr::Node* node = new nr::Node{r.get<0>()};

      std::unique_lock<std::mutex> lock{init_mutex};
      nodes[node_id] = std::unique_ptr<nr::Node>{node};
      thread_owned_contexts[node_id] = r.get<1>();
      ++nodes_init;

      if (nodes_init == num_replicas())
        all_nodes_init.notify_all();
    }

    std::unique_lock<std::mutex> lock{init_mutex};
    while (nodes_init < num_replicas())
      all_nodes_init.wait(lock);

    const uint32_t context_index = core_id / num_replicas();

    std::cerr << "thread on core_id " << core_id
              << " registered with node_id " << node_id
              << " context " << context_index
              << std::endl;

    return &(thread_owned_contexts[node_id].ptr[context_index]).a;
  }
};

/*
  //LogWrapper& lw = createLog();
  //ReplicaWrapper* rw = createReplica(lw);
  //auto tkn = rw->RegisterWrapper();
  //rw->ReplicaMap(tkn, 0x2000, 0x3000);
  //rw->ReplicaResolve(tkn, 0x2000);
*/

class nr_rust_helper {
  uint32_t n_threads_per_replica;
  LogWrapper& log;
  std::mutex init_mutex;
  size_t nodes_init;
  std::vector<ReplicaWrapper*> nodes;
  std::condition_variable all_nodes_init;

 public:
  static size_t num_replicas() {
    return NRConstants_Compile::__default::NUM__REPLICAS;
  }

  nr_rust_helper(size_t n_threads)
    : n_threads_per_replica{static_cast<uint32_t>(n_threads / num_replicas())}
    , log{createLog()}
    , init_mutex{}
    , nodes_init{}
    , nodes{}
    , all_nodes_init{}
  {
    nodes.resize(num_replicas());
    assert(num_replicas() > 0);
    assert(num_replicas() <= n_threads);
    assert(n_threads_per_replica * num_replicas() == n_threads);
  }

  ~nr_rust_helper() {
    // NYI
  }

  static uint32_t get_node_id(uint32_t core_id) {
    return core_id % 4;
  }

  ReplicaWrapper *get_node(uint32_t core_id)
  {
    return nodes[get_node_id(core_id)];
  }

  void init_nr() {}

  size_t register_thread(uint32_t core_id) {
    std::unique_lock<std::mutex> lock{init_mutex};
    uint64_t node_id = core_id % 4;

    if (core_id / num_replicas() == 0)
    {
      auto replica = createReplica(log);
      std::cerr << "thread on core_id " << core_id
                << " done initializing node_id " << node_id << std::endl;
      nodes[node_id] = replica;
      ++nodes_init;

      if (nodes_init == num_replicas())
        all_nodes_init.notify_all();
    }

    while (nodes_init < num_replicas())
      all_nodes_init.wait(lock);

    // TODO(stutsman) no pinning, affinity, and threads on different
    // nodes may actually use the wrong replica; all this needs to be
    // fixed if we want to use this harness.
    auto context = nodes[node_id]->RegisterWrapper();

    std::cerr << "thread on core_id" << core_id
              << " registered with node_id " << node_id
              << " context " << context
              << std::endl;

    return context;
  }
};

#endif
