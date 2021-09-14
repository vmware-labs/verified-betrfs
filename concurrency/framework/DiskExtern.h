#pragma once

#include <cassert>
#include <cstdio>
#include <cstdint>
#include <cassert>
#include <fcntl.h>
#include <unistd.h>
#include <cerrno>
#include <cstdlib>
#include <libaio.h>

#include "Extern.h"

static_assert(sizeof(long long) == 8);
static_assert(sizeof(size_t) == 8);
static_assert(sizeof(off_t) == 8);
static_assert(sizeof(uintptr_t) == 8);

namespace InstantiatedDiskInterface {
  extern int fd;

  struct IOCtx {
    io_context_t* ctx;
  };

  inline IOCtx get_IOCtx_default() {
    IOCtx ioctx;
    ioctx.ctx = NULL;
    return ioctx;
  }

  inline IOCtx init__ctx() {
    IOCtx ioctx;
    ioctx.ctx = new io_context_t;
    int ret = io_setup(256, ioctx.ctx);
    if (ret != 0) {
      std::cerr << "io_setup failed" << std::endl;
      exit(1);
    }
    return ioctx;
  }

  inline bool operator==(const IOCtx &left, const IOCtx &right) {
    std::cerr << "Error: IOCtx == called" << std::endl;
    exit(1);
  }

  inline void async__submit(IOCtx& ioctx, Ptrs::Ptr i) {
    iocb* iocb_ptr = (iocb*) i.ptr;
    int ret = io_submit(*ioctx.ctx, 1, &iocb_ptr);
    //printf("%d\n", ret);
    //printf("%d %d %d %d %d %d\n",
    //    EAGAIN, EBADF, EFAULT, EINVAL, ENOSYS, EPERM);
    if (ret != 1) {
      std::cerr << "io_submit failed" << std::endl;
      exit(1);
    }
  }

  inline void async__read(IOCtx& ioctx, Ptrs::Ptr i) {
    async__submit(ioctx, i);
  }

  inline void async__write(IOCtx& ioctx, Ptrs::Ptr i) {
    async__submit(ioctx, i);
  }

  inline void sync__read(Ptrs::Ptr buf, uint64 nbytes, int64_t offset)
  {
    int ret = pread(fd, (void*)buf.ptr, nbytes, offset * 4096);
    if (ret != 0) {
      std::cerr << "pread failed" << std::endl;
      exit(1);
    }
  }

  inline Ptrs::Ptr get__event(IOCtx& ioctx) {
    struct io_event event;
    int status = io_getevents(*ioctx.ctx, 0, 1, &event, NULL);
    if (status == 0) return Ptrs::null_ptr();
    assert (status == 1);
    assert (event.res > 0);
    iocb* i = event.obj;
    return Ptrs::Ptr((uintptr_t)i);
  }
}

namespace IocbStruct {
  inline Ptrs::Ptr new__iocb() {
    return Ptrs::Ptr((uintptr_t)(new iocb));
  }

  inline Ptrs::Ptr new__iocb__array(uint64_t len) {
    return Ptrs::Ptr((uintptr_t)(new iocb[len]));
  }

  inline void iocb__prepare__read(Ptrs::Ptr i, int64_t offset, uint64_t nbytes, Ptrs::Ptr buf) {
    io_prep_pread((iocb *)i.ptr, InstantiatedDiskInterface::fd,
        (void*)buf.ptr, nbytes, offset * 4096);
  }

  inline void iocb__prepare__write(Ptrs::Ptr i, int64_t offset, uint64_t nbytes, Ptrs::Ptr buf) {
    io_prep_pwrite((iocb *)i.ptr, InstantiatedDiskInterface::fd,
        (void*)buf.ptr, nbytes, offset * 4096);
  }

  inline uint64_t SizeOfIocb() {
    return sizeof(iocb);
  }
}

template <>
struct std::hash<InstantiatedDiskInterface::IOCtx> {
  std::size_t operator()(const InstantiatedDiskInterface::IOCtx& x) const {
    std::cerr << "Error: Cell hash called" << std::endl;
    exit(1);
  }
};

