// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#include <semaphore>

namespace Mutexes {

template <typename V>
struct InternalMutex {
  std::binary_semaphore semaphore;
  V v;

  InternalMutex(V const& v) : semaphore(1), v(v) { }
};

using Mutex<V> = InternalMutex<V>*;

template <typename V>
Mutex<V> new__mutex(V v)
{
  return new InternalMutex(v);
}

template <typename V>
Mutex<V> acquire(Mutex m)
{
  m->semaphore.acquire();
  return m->v;
}

template <typename V>
Mutex<V> release(Mutex m, V v)
{
  m->v = v;
  m->semaphore.release();
}

}
