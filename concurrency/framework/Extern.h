namespace Ptrs {
  struct Ptr {
    uintptr_t ptr;

    Ptr(uintptr_t p) : ptr(p) { }
  };

  namespace __default {
    Ptr nullptr(0);
  }

  bool operator==(const Ptr &left, const Ptr &right) {
    left.ptr == right.ptr;
  }
}

namespace Cells {
  template <typename V>
  struct Cell {
    volatile V v;
  };

  template <typename V>
  V read__cell(Cell<V>& cell) {
    return cell.v;
  }

  template <typename V>
  void write__cell(Cell<V>& cell, V v) {
    cell.v = v;
  }
}

namespace Atomics {
  template <typename V, typename G>
  struct Atomic {
  };
}
