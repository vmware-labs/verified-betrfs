// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

//#include <semaphore> // c++20 feature
#include <mutex>
#include <condition_variable>

namespace Mutexes {

class BinarySemaphore {
public:
  BinarySemaphore (int count) : count(count) { }
  
  void release() {
    std::unique_lock<std::mutex> lock(mtx);
    count++;
    cv.notify_one();
  }

  void acquire() {
    std::unique_lock<std::mutex> lock(mtx);
    while (count == 0) {
      cv.wait(lock);
    }
    count--;
  }

private:
  // TODO mutex has ACQUIRE/RELEASE semantics, not seq consistent semantics
  // can't use mutex here
  //std::mutex mtx;

  std::condition_variable cv;
  volatile int count;
};

template <typename V>
struct InternalMutex {
  // We use a semaphore because it allows us to do the 'release'
  // on a different thread from the 'acquire'.
  // This behavior is allowed by the Dafny spec of Mutex.
  // Howeer, that action would result in undefined behavior for std::mutex.

  //std::binary_semaphore semaphore;
  BinarySemaphore semaphore;
  volatile V v;

  InternalMutex(V const& v) : semaphore(1), v(v) { }
};

template <typename V>
using Mutex = InternalMutex<V>*;

template <typename V>
Mutex<V> new__mutex(V v)
{
  return new InternalMutex(v);
}

template <typename V>
V acquire(Mutex<V> m)
{
  m->semaphore.acquire();
  return m->v;
}

template <typename V>
void release(Mutex<V> m, V v)
{
  m->v = v;
  m->semaphore.release();
}

}
