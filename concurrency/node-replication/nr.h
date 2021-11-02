#ifndef NR_H
#define NR_H

#include "DafnyRuntime.h"

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
    assert(node_creation_tokens->size() == NUM_REPLICAS);
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

      if (nodes.size() == NUM_REPLICAS)
        all_nodes_init.notify_all();
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

#endif