#include <iostream>
#include <cstdlib>

namespace Ptrs {
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
    volatile V v;

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
}

template <typename V, typename G>
struct std::hash<Atomics::Atomic<V, G>> {
  std::size_t operator()(const Atomics::Atomic<V, G>& x) const {
    std::cerr << "Error: Atomic hash called" << std::endl;
    exit(1);
  }
};

