#pragma once

#include "DafnyRuntime.h"
#include "LinearExtern.h"

#include <iostream>
#include <cstdlib>
#include <chrono>
#include <thread>
#include <atomic>

namespace Ptrs {
  static_assert(sizeof(uintptr_t) == 8);
  
  struct Ptr {
    uintptr_t ptr;

    Ptr() : ptr(0) { }
    explicit Ptr(uintptr_t p) : ptr(p) { }

    template <typename V>
    void index__write(uint64_t i, V v) {
      *(((V*)ptr) + i) = v;
    }

    template <typename V>
    V index__read(uint64_t i) {
      return *(((V*)ptr) + i);
    }

    Ptr* operator->() { return this; }
  };

  inline Ptr null_ptr() {
    return Ptr(0);
  }

  inline Ptr get_Ptr_default() {
    return Ptr(0);
  }

  inline bool operator==(const Ptr &left, const Ptr &right) {
    return left.ptr == right.ptr;
  }

  inline Ptr ptr__add(Ptr p, uint64 a) {
    return Ptr(p.ptr + a);
  }

  inline uint64_t ptr__diff(Ptr p, Ptr q) {
    return p.ptr - q.ptr;
  }

  template <typename V>
  Ptr alloc__array__aligned(uint64_t len, V init_v, uint64_t alignment) {
    // TODO should check len * sizeof(V) <= max size_t
    V* ptr;
    int res = posix_memalign((void**)&ptr, alignment, len * sizeof(V));
    if (res != 0) {
      std::cerr << "posix_memalign failed" << std::endl;
      exit(1);
    }
    for (uint64_t i = 0; i < len; i++) {
      new (&ptr[i]) V(init_v);
    }
    return Ptr((uintptr_t)ptr);
  }

  template <typename V>
  Ptr alloc__array(uint64_t len, V init_v) {
    // TODO should check len * sizeof(V) <= max size_t
    V* ptr = (V*)malloc(len * sizeof(V));
    if (ptr == nullptr) {
      std::cerr << "malloc failed" << std::endl;
      exit(1);
    }
    for (uint64_t i = 0; i < len; i++) {
      new (&ptr[i]) V(init_v);
    }
    return Ptr((uintptr_t)ptr);
  }

  template <typename V>
  uint64_t sizeof_() {
    return sizeof(V);
  }
}

namespace Cells {
  template <typename V>
  struct Cell {
    mutable V v;

    Cell() : v(get_default<V>::call()) { }
    explicit Cell(V v) : v(v) { }

    Cell(Cell const& other) : v(other.v) { }

    Cell<V>& operator=(const Cell<V>& other)
    {
      this->v = other.v;
      return *this;
    }
  };

  template <typename V>
  Cell<V> get_Cell_default() {
    return Cell<V>();
  }

  template <typename V>
  Cell<V> new__cell(V v) {
    return Cell(v);
  }

  template <typename V>
  V read__cell(Cell<V>& cell) {
    return cell.v;
  }

  template <typename V>
  void write__cell(Cell<V>& cell, V v) {
    cell.v = v;
  }

  template <typename V>
  bool operator==(const Cell<V> &left, const Cell<V> &right) {
    std::cerr << "Error: Cell == called" << std::endl;
    exit(1);
  }
};

template <typename T>
struct get_default<LinearExtern::linear_seq<T>> {
  static LinearExtern::linear_seq<T> call() {
    return nullptr;
  }
};

namespace LinearCells {
  template <typename V>
  struct Linearization
  {
    using linear_type = V;
    using shared_type = V;
  };

  template <typename T>
  struct Linearization<DafnySequence<T>>
  {
    using linear_type = LinearExtern::linear_seq<T>;
    using shared_type = LinearExtern::shared_seq<T>;
  };

  template <typename V>
  struct LinearCell {
    mutable typename Linearization<V>::linear_type v;

    LinearCell() : v(get_default<typename Linearization<V>::linear_type>::call()) { }
    //explicit LinearCell(typename Linearization<V>::linear_type v) : v(v) { }

    LinearCell(LinearCell const& other) : v(other.v) { }

    LinearCell<V>& operator=(const LinearCell<V>& other)
    {
      this->v = other.v;
      return *this;
    }
  };

  template <typename V>
  LinearCell<V> get_LinearCell_default() {
    return LinearCell<V>();
  }

  template <typename V>
  LinearCell<V> new__lcell() {
    return LinearCell<V>();
  }

  template <typename V>
  typename Linearization<V>::shared_type* read__lcell(LinearCell<V>& cell) {
    return &cell.v;
  }

  template <typename V>
  void give__lcell(LinearCell<V>& cell, typename Linearization<V>::linear_type v) {
    cell.v = v;
  }

  template <typename V>
  typename Linearization<V>::linear_type take__lcell(LinearCell<V>& cell) {
    return cell.v;
  }

  template <typename V>
  bool operator==(const LinearCell<V> &left, const LinearCell<V> &right) {
    std::cerr << "Error: LinearCell == called" << std::endl;
    exit(1);
  }
};

template <typename V>
struct std::hash<Cells::Cell<V>> {
  std::size_t operator()(const Cells::Cell<V>& x) const {
    std::cerr << "Error: Cell hash called" << std::endl;
    exit(1);
  }
};

template <typename V>
struct std::hash<LinearCells::LinearCell<V>> {
  std::size_t operator()(const LinearCells::LinearCell<V>& x) const {
    std::cerr << "Error: Cell hash called" << std::endl;
    exit(1);
  }
};

template <typename V>
struct get_default<Cells::Cell<V> > {
  static Cells::Cell<V> call() {
    return Cells::Cell<V>();
  }
};

namespace Atomics {
  template <typename V, typename G>
  struct Atomic {
    std::atomic<V> slot;

    Atomic() { }
    explicit Atomic(V v) : slot(v) { }

    // std::atomic deletes the copy & assignment operators so we need to re-define them.
    // Ideally, we would transfer ownership of a `linear Atomic` (and other linear objects)
    // via move constructors. Right now that isn't the case - though we can still rely on
    // the the linear type system to enforce that things aren't used after they are
    // "moved" (but actually copied).

    Atomic(Atomic<V, G> const& self)
      : slot(self.slot.load()) { }

    Atomic<V, G>& operator=(const Atomic<V, G>& other)
    {
      slot.store(other.slot.load());
      return *this;
    }
  };

  template <typename V, typename G>
  Atomic<V, G> get_Atomic_default() {
    return Atomic<V, G>();
  }

  template <typename V, typename G>
  bool operator==(const Atomic<V, G> &left, const Atomic<V, G> &right) {
    std::cerr << "Error: Atomic == called" << std::endl;
    exit(1);
  }

  template <typename V, typename G>
  Atomic<V, G> new__atomic(V v) {
    Atomic<V, G> ia(v);
    return ia;
  }

  template <typename V>
  void new__ghost__atomic() {
  }

  template <typename V, typename G>
  bool execute__atomic__compare__and__set__strong(
      Atomic<V, G>& a,
      V v1,
      V v2)
  {
    return a.slot.compare_exchange_strong(v1, v2, std::memory_order_seq_cst);
  }

  template <typename V, typename G>
  bool execute__atomic__compare__and__set__weak(
      Atomic<V, G>& a,
      V v1,
      V v2)
  {
    return a.slot.compare_exchange_weak(v1, v2, std::memory_order_seq_cst);
  }

  template <typename V, typename G>
  V execute__atomic__load(
      Atomic<V, G>& a)
  {
    return a.slot.load(std::memory_order_seq_cst);
  }

  template <typename V, typename G>
  void execute__atomic__noop()
  {
  }

  template <typename V, typename G>
  void execute__atomic__store(
      Atomic<V, G>& a,
      V v)
  {
    a.slot.store(v, std::memory_order_seq_cst);
  }

  template <typename V, typename G>
  V execute__atomic__fetch__or(
      Atomic<V, G>& a,
      V v)
  {
    return a.slot.fetch_or(v, std::memory_order_seq_cst);
  }

  template <typename V, typename G>
  V execute__atomic__fetch__and(
      Atomic<V, G>& a,
      V v)
  {
    return a.slot.fetch_and(v, std::memory_order_seq_cst);
  }

  template <typename V, typename G>
  V execute__atomic__fetch__xor(
      Atomic<V, G>& a,
      V v)
  {
    return a.slot.fetch_xor(v, std::memory_order_seq_cst);
  }

  template <typename V, typename G>
  V execute__atomic__fetch__add(
      Atomic<V, G>& a,
      V v)
  {
    return a.slot.fetch_add(v, std::memory_order_seq_cst);
  }

  template <typename V, typename G>
  V execute__atomic__fetch__sub(
      Atomic<V, G>& a,
      V v)
  {
    return a.slot.fetch_sub(v, std::memory_order_seq_cst);
  }

  // Dafny doesn't have generics over numeric types
  // so we have to define the arithmetic actions
  // over all integer precisions individually,
  // e.g., execute__atomic__fetch__sub__uint8

  #define ARITH_SPECIALIZE(t, name) \
    template<typename G> \
    t execute__atomic__fetch__sub__ ## name (Atomic<t, G>& a, t v) { \
        return execute__atomic__fetch__sub<t, G>(a, v); } \
        \
    template<typename G> \
    t execute__atomic__fetch__add__ ## name (Atomic<t, G>& a, t v) { \
        return execute__atomic__fetch__add<t, G>(a, v); } \
        \
    template<typename G> \
    t execute__atomic__fetch__or__ ## name (Atomic<t, G>& a, t v) { \
        return execute__atomic__fetch__or<t, G>(a, v); } \
        \
    template<typename G> \
    t execute__atomic__fetch__xor__ ## name (Atomic<t, G>& a, t v) { \
        return execute__atomic__fetch__xor<t, G>(a, v); } \
        \
    template<typename G> \
    t execute__atomic__fetch__and__ ## name (Atomic<t, G>& a, t v) { \
        return execute__atomic__fetch__and<t, G>(a, v); } \

  ARITH_SPECIALIZE(uint8_t, uint8)
  ARITH_SPECIALIZE(uint16_t, uint16)
  ARITH_SPECIALIZE(uint32_t, uint32)
  ARITH_SPECIALIZE(uint64_t, uint64)

  static_assert(std::atomic<uint8_t>::is_always_lock_free);
  static_assert(std::atomic<uint16_t>::is_always_lock_free);
  static_assert(std::atomic<uint32_t>::is_always_lock_free);
  static_assert(std::atomic<uint64_t>::is_always_lock_free);
}

template <typename V, typename G>
struct std::hash<Atomics::Atomic<V, G>> {
  std::size_t operator()(const Atomics::Atomic<V, G>& x) const {
    std::cerr << "Error: Atomic hash called" << std::endl;
    exit(1);
  }
};

template <typename V, typename G>
struct get_default<Atomics::Atomic<V, G> > {
  static Atomics::Atomic<V, G> call() {
    return Atomics::Atomic<V, G>();
  }
};

namespace ThreadUtils {
  inline void sleep(uint64_t ns) {
    std::this_thread::sleep_for(std::chrono::nanoseconds(ns));
  }

  inline void pause() {
    __builtin_ia32_pause();
  }
}
