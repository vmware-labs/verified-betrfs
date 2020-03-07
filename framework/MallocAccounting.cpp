#include <stdlib.h>
#include <stdio.h>
#include <malloc.h>

#include "MallocAccounting.h"

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wdeprecated-declarations"

// Based on malloc hooks, which are "deprecated", and yet still in play.
// https://www.gnu.org/savannah-checkouts/gnu/libc/manual/html_node/Hooks-for-Malloc.html
//
// if we ever have to get fancy, here's LD_PRELOAD route:
// http://truthbk.github.io/hooking-malloc-libcs-facilities-vs-ld_preload/

extern "C" {

typedef void* (*volatile malloc_f)(size_t size, const void*);
typedef void (*volatile free_f)(void*, const void*);

static malloc_f old_malloc_hook;
static free_f old_free_hook;
static void *malloc_hook(size_t size, const void *caller);
static void free_hook(void* ptr, const void *caller);

static inline void record_underlying_hooks() {
  old_malloc_hook = __malloc_hook;
  old_free_hook = __free_hook;
}

static inline void install_hooks() {
  __malloc_hook = malloc_hook;
  __free_hook = free_hook;
}

static inline void remove_hooks() {
  __malloc_hook = old_malloc_hook;
  __free_hook = old_free_hook;
}
  
void init_malloc_accounting() {
  record_underlying_hooks();
  install_hooks();
}

void *malloc_hook(size_t size, const void *caller) {
  void *result;

  remove_hooks();

  // Call real malloc
  result = malloc(size);
  //record_underlying_hooks(); // not sure why example re-saves hooks here

  // do our work (outside of hookland)
  printf("malloc_hook sees size %lx from %p; returns %p\n", size, caller, result);

  install_hooks();

  return result;
}

void free_hook(void* ptr, const void *caller) {
  remove_hooks();

  // Call real malloc
  free(ptr);

  // do our work (outside of hookland)
  printf("malloc_hook sees free %p from %p\n", ptr, caller);

  install_hooks();
}

//void *__real___libc_malloc(size_t size);
//void __real___libc_free(void* ptr);
//
//void *__wrap___libc_malloc(size_t size)
//{
//  size_t underlying_size = sizeof(size_t) + size;
//  void* ptr = __real___libc_malloc(underlying_size);
//
//  size_t* sptr = (size_t*) ptr;
//  sptr[0] = size;
//  void* vptr = (void*) (&sptr[1]);
//  printf("My malloc underlying %p vptr %p size %lx underlying size %lx\n", ptr, vptr, size, underlying_size);
//  return vptr;
//}
//
//void __wrap___libc_free(void* vptr)
//{
//  size_t* sptr = (size_t*) vptr;
//  size_t size = sptr[-1];
//  void* ptr = (void*) (&sptr[-1]);
//  printf("  My free underlying %p vptr %p size %lx\n", ptr, vptr, size);
//  __real___libc_free(ptr);
//}

}
