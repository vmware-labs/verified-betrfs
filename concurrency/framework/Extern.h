#include <iostream>
#include <cstdlib>

namespace Ptrs {
  static_assert(sizeof(uintptr_t) == 8);
  
  struct Ptr {
    uintptr_t ptr;

    Ptr() : ptr(0) { }
    Ptr(uintptr_t p) : ptr(p) { }
  };

  namespace __default {
    Ptr null_ptr(0);
  }

  Ptr get_Ptr_default() {
    return Ptr(0);
  }

  bool operator==(const Ptr &left, const Ptr &right) {
    return left.ptr == right.ptr;
  }
}

template <>
struct std::hash<Ptrs::Ptr> {
  std::size_t operator()(const Ptrs::Ptr& x) const {
    size_t seed = 0;
    hash_combine<uintptr_t>(seed, x.ptr);
    return seed;
  }
};

namespace Cells {
  template <typename V>
  struct Cell {
    mutable volatile V v;

    Cell() : v(get_default<V>::call()) { }
  };

  template <typename V>
  Cell<V> get_Cell_default() {
    return Cell<V>();
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

template <typename V>
struct std::hash<Cells::Cell<V>> {
  std::size_t operator()(const Cells::Cell<V>& x) const {
    std::cerr << "Error: Cell hash called" << std::endl;
    exit(1);
  }
};

namespace Atomics {
  template <typename V, typename G>
  struct Atomic {
    std::atomic<V> slot;

    Atomic() { }
    Atomic(V v) : slot(v) { }

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

  template <typename V, typename G>
  bool execute__atomic__compare__and__set__strong(
      Atomic<V, G>& a,
      V v1,
      V v2)
  {
    a.slot.compare_exchange_strong(v1, v2, std::memory_order_seq_cst);
  }

  template <typename V, typename G>
  V execute__atomic__load(
      Atomic<V, G>& a)
  {
    return a.slot.load(std::memory_order_seq_cst);
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


