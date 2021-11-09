#include "./vspace/target/cxxbridge/vspace/src/lib.rs.h"
using VSpacePtr = VSpace*;

inline VSpacePtr get_VSpacePtr_default() {
    return createVSpace();
}
