/*#include <libaio.h>
#include <cstdio>
#include <cstdint>
#include <cassert>
#include <fcntl.h>
#include <unistd.h>
#include <cerrno>*/
#include <cstdlib>

namespace InstantiatedDiskInterface {
  extern int fd;

  struct IOCtx {
    //io_context_t* ctx;
  };

  inline IOCtx get_IOCtx_default();

  inline bool operator==(const IOCtx &left, const IOCtx &right) {
    std::cerr << "Error: IOCtx == called" << std::endl;
    exit(1);
  }
}

template <>
struct std::hash<InstantiatedDiskInterface::IOCtx> {
  std::size_t operator()(const InstantiatedDiskInterface::IOCtx& x) const {
    std::cerr << "Error: Cell hash called" << std::endl;
    exit(1);
  }
};

