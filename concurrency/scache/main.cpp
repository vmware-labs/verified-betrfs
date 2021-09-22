#include <iostream>
#include <sys/stat.h>
#include <sys/types.h>
#include <stdio.h>
#include <fcntl.h>
#include <cassert>

#include "DafnyRuntime.h"
#include "Extern.h"
#include "LinearExtern.h"
#include "DiskExtern.h"
#include "Application.i.h"

namespace InstantiatedDiskInterface {
  int fd;
}

using InstantiatedDiskInterface::fd;

void init_fd() {
  //fd = open(".vericache",
  //    O_RDWR | O_DIRECT | O_DSYNC | O_NOATIME | O_CREAT, S_IRUSR | S_IWUSR);
  fd = open(".vericache", O_RDWR | O_DIRECT | O_DSYNC | O_NOATIME);
  if (fd < 0) {
    std::cerr << "File open failed" << std::endl;
  }
}

struct Cache {
  CacheTypes_29_ON_TheAIO__Compile::Cache c;
};

struct ThreadLocal {
  CacheTypes_29_ON_TheAIO__Compile::LocalState s;
};

Cache init_cache() {
  Cache cache;
  cache.c = Application_28_ON_TheAIO__Compile::__default::init();
  return cache;
}

ThreadLocal init_thread_local_state(uint64_t t) {
  ThreadLocal tl;
  tl.s = Application_28_ON_TheAIO__Compile::__default::init__thread__local__state(t);
  return tl;
}

DafnySequence<uint8> read_block(Cache& cache, ThreadLocal& tl, uint64_t disk_addr) {
  return Application_28_ON_TheAIO__Compile::__default::read__block(cache.c, tl.s, disk_addr);
}

void write_block(Cache& cache, ThreadLocal& tl, uint64_t disk_addr, DafnySequence<uint8> bytes) {
  Application_28_ON_TheAIO__Compile::__default::write__block(cache.c, tl.s, disk_addr, bytes);
}

Cache global_cache;
thread_local ThreadLocal local_state;

void write_int(uint64_t disk_addr, uint8_t b) {
  auto d = DafnySequence<uint8_t>(4096);
  d = d.update(0, b);
  write_block(global_cache, local_state, disk_addr, d);
  std::cout << "write: " << disk_addr << " value " << (int)b << std::endl;
}

uint8_t read_int(uint64_t disk_addr) {
  auto d = read_block(global_cache, local_state, disk_addr);
  uint8_t res = d.select(0);
  std::cout << "read: " << disk_addr << " value " << (int)res << std::endl;
  return res;
}

void thread1() {
  local_state = init_thread_local_state(0);

  for (int i = 0; i < 1050; i++) {
    write_int(i, (uint8_t)(i % 256));
  }

  for (int i = 0; i < 1050; i++) {
    read_int(i);
  }
}

void thread2() {
  local_state = init_thread_local_state(0);

  for (int i = 0; i < 1050; i++) {
    write_int(10000 + i, (uint8_t)(i % 256));
  }

  for (int i = 0; i < 1050; i++) {
    read_int(10000 + i);
  }
}

int main() {
  init_fd();

  global_cache = init_cache();
  std::cout << "cache initialized" << std::endl;

  std::thread t1(thread1);
  std::thread t2(thread2);

  t1.join();
  t2.join();
}
