#include <libaio.h>
#include <cstdio>
#include <cstdint>
#include <cassert>
#include <fcntl.h>

       #include <unistd.h>
       #include <cerrno>

#define O_DIRECT_FLAG (0)
#if USE_DIRECT
#ifdef O_DIRECT
#undef O_DIRECT_FLAG
#define O_DIRECT_FLAG O_DIRECT
#endif
#endif

static_assert(sizeof(long long) == 8);
static_assert(sizeof(size_t) == 8);
static_assert(sizeof(off_t) == 8);
static_assert(sizeof(uintptr_t) == 8);

io_context_t ctx;
int fd = 0;

uintptr_t new__iocb() {
  return (uintptr_t)(new iocb);
}

void iocb__prepare__read(uintptr_t i, int64_t offset, uint64_t nbytes, uintptr_t buf) {
  io_prep_pread((iocb *)i, fd, (void*)buf, nbytes, offset);
}

void iocb__prepare__write(uintptr_t i, int64_t offset, uint64_t nbytes, uintptr_t buf) {
  io_prep_pwrite((iocb *)i, fd, (void*)buf, nbytes, offset);
}

void async__submit(uintptr_t i) {
  iocb* iocb_ptr = (iocb*) i;
  int ret = io_submit(ctx, 1, &iocb_ptr);
  //printf("%d\n", ret);
  //printf("%d %d %d %d %d %d\n",
  //    EAGAIN, EBADF, EFAULT, EINVAL, ENOSYS, EPERM);
  assert(ret == 1);
}

#define async__read async__submit
#define async__write async__submit

void sync__read(uintptr_t buf, nbytes: uint64, offset: int64_t)
{
  pread(fd, (void*)buf, nbytes, offset);
}

uintptr_t get__event() {
  struct io_event event;
  int status = io_getevents(ctx, 0, 1, &event, NULL);
  if (status == 0) return NULL;
  assert (status == 1);
  assert (event.res > 0);
  iocb* i = event.obj;
  return i;
}

int main() {
  fd = open("stuff.txt", O_RDWR | O_DIRECT_FLAG | O_DSYNC | O_NOATIME);
  printf("fd = %d\n", fd);
  io_setup(100, &ctx);

  char stuff[27] = "abcdefghijklmnopqrstuvwxyz";

  uintptr_t a = new__iocb();
  iocb__prepare__write(a, 0, 26, stuff);
  async__submit(a);
  get__event();
}
