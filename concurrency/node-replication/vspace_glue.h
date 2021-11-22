#include "DafnyRuntime.h"
#include "./vspace/target/cxxbridge/vspace/src/lib.rs.h"
using VSpacePtr = VSpace*;

inline VSpacePtr get_VSpacePtr_default() {
    return NULL;
}

template <>
struct get_default<VSpacePtr> {
  static VSpacePtr call() {
    return get_VSpacePtr_default();
  }
};
