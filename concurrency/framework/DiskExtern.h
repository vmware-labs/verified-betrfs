#pragma once

/*#include <libaio.h>
#include <cstdio>
#include <cstdint>
#include <cassert>
#include <fcntl.h>
#include <unistd.h>
#include <cerrno>*/
#include <cstdlib>

#include "Extern.h"

static_assert(sizeof(long long) == 8);
static_assert(sizeof(size_t) == 8);
static_assert(sizeof(off_t) == 8);
static_assert(sizeof(uintptr_t) == 8);

namespace IocbStruct {
  uintptr_t new__iocb(); /*{
    return (uintptr_t)(new iocb);
  }*/

  void iocb__prepare__read(Ptrs::Ptr i, int64_t offset, uint64_t nbytes, Ptrs::Ptr buf); /*{
    io_prep_pread((iocb *)i, fd, (void*)buf, nbytes, offset);
  }*/

  void iocb__prepare__write(Ptrs::Ptr i, int64_t offset, uint64_t nbytes, Ptrs::Ptr buf); /*{
    io_prep_pwrite((iocb *)i, fd, (void*)buf, nbytes, offset);
  } */

  inline uint64_t SizeOfIocb();
}

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

  void async__submit(IOCtx& ioctx, Ptrs::Ptr i); /* {
    iocb* iocb_ptr = (iocb*) i;
    int ret = io_submit(ctx, 1, &iocb_ptr);
    //printf("%d\n", ret);
    //printf("%d %d %d %d %d %d\n",
    //    EAGAIN, EBADF, EFAULT, EINVAL, ENOSYS, EPERM);
    assert(ret == 1);
  }*/

  inline void async__read(IOCtx& ioctx, Ptrs::Ptr i) {
    async__submit(ioctx, i);
  }

  inline void async__write(IOCtx& ioctx, Ptrs::Ptr i) {
    async__submit(ioctx, i);
  }

  void sync__read(Ptrs::Ptr buf, uint64 nbytes, int64_t offset);
  /*
  {
    pread(fd, (void*)buf, nbytes, offset);
  }*/

  Ptrs::Ptr get__event(IOCtx& ioctx); /* {
    struct io_event event;
    int status = io_getevents(ctx, 0, 1, &event, NULL);
    if (status == 0) return NULL;
    assert (status == 1);
    assert (event.res > 0);
    iocb* i = event.obj;
    return i;
  }*/
}

template <>
struct std::hash<InstantiatedDiskInterface::IOCtx> {
  std::size_t operator()(const InstantiatedDiskInterface::IOCtx& x) const {
    std::cerr << "Error: Cell hash called" << std::endl;
    exit(1);
  }
};

