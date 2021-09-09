namespace Ptrs_Compile {
  using Ptr = uintptr_t;
}

namespace Cells_Compile {
  template <typename V>
  struct Cell {
    volatile V v;
  };
}

namespace Atomics {
  template <typename V, typename G>
  struct Atomic {
  };
}
