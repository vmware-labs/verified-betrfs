#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <malloc.h>
#include <assert.h>
#include <string.h>

#include "MallocAccounting.h"

#if MALLOC_ACCOUNTING

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wdeprecated-declarations"

// Based on malloc hooks, which are "deprecated", and yet still in play.
// https://www.gnu.org/savannah-checkouts/gnu/libc/manual/html_node/Hooks-for-Malloc.html
//
// if we ever have to get fancy, here's LD_PRELOAD route:
// http://truthbk.github.io/hooking-malloc-libcs-facilities-vs-ld_preload/

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

#define ACCOUNTING_MAGIC 0x1badf00f

struct ARow;

// A little header we prepend to each allocation so we can track the
// allocation size so we know what to free later.
typedef struct {
  uint64_t magic; // identify my own mallocs
  size_t allocation_size;
  ARow* arow;
} AccountingHeader;

struct Label {
  const char* scope;
  const char* subscope;
  Label(const char* scope, const char* subscope)
    : scope(scope),
      subscope(subscope) {}
  Label() { scope = NULL; }
  bool equals(const Label& other) const {
    return strcmp(scope, other.scope) == 0
      && strcmp(subscope, other.subscope) == 0;
  }
};

struct ARow {
  Label label;
  int total_allocation_count;
  int open_allocation_count;
  int total_allocation_bytes;
  int open_allocation_bytes;
  ARow()
    : label(),
      total_allocation_count(0),
      open_allocation_count(0),
      total_allocation_bytes(0),
      open_allocation_bytes(0)
  {}
};

// Somebody wishes he had a hashtable, doesn't somebody?
#define NUM_ROWS 1000
Label g_default_label("default", "");
class ATable {
private:
  ARow rows[NUM_ROWS];
  Label g_active_label;

  // returns index of row with label, or index of next free row.
  int get_or_add_row_index(const Label& label);

public:
  ATable();

  void set_active_label(const Label& label) {
    assert(g_active_label.equals(g_default_label)); // nested label calls; need label stack?
    g_active_label = label;
  }
  void clear_active_label() { g_active_label = g_default_label; }

  // Add a row to the table if it's absent.
  ARow* get_or_add_row(const Label& label);

  ARow* get_active_row() { return get_or_add_row(g_active_label); }

  void display();
};

ATable::ATable() {
  g_active_label = g_default_label;
  for (int i=0; i<NUM_ROWS; i++) {
    rows[i].label = Label();
  }
}

int ATable::get_or_add_row_index(const Label& label) {
  assert(label.scope != NULL);
  int i;
  for (i=0; i<NUM_ROWS && rows[i].label.scope!=NULL; i++) {
    if (label.equals(rows[i].label)) {
       return i;
    }
  }
  assert(i<NUM_ROWS); // table full!
  return i;
}

ARow* ATable::get_or_add_row(const Label& label)
{
  int index = get_or_add_row_index(label);
  assert(index < NUM_ROWS);
  ARow* arow = &rows[index];
  if (arow->label.scope != NULL) {
    return arow;  // already present
  }
  arow->label = label;
  return arow;
}

void ATable::display() {
  printf("%10s %10s %10s %10s  %s\n",
    "tot cnt", "open cnt", "tot byt", "open byt", "label");
  printf("%10s %10s %10s %10s  %s\n",
    "-------", "--------", "-------", "--------", "----------");
  for (int i=0; i<NUM_ROWS && rows[i].label.scope!=NULL; i++) {
    ARow* row = &rows[i];
    printf("%10d %10d %10d %10d  %s.%s\n",
      row->total_allocation_count,
      row->open_allocation_count,
      row->total_allocation_bytes,
      row->open_allocation_bytes,
      row->label.subscope,
      row->label.scope);
  }
}

ATable atable;

void *malloc_hook(size_t size, const void *caller) {
  void *result;

  remove_hooks();

  // Call real malloc
  result = malloc(size + sizeof(AccountingHeader));

  ARow* arow = atable.get_active_row();
  AccountingHeader* ar = (AccountingHeader*) result;
  result = (char*) result + sizeof(AccountingHeader);
  ar->magic = ACCOUNTING_MAGIC;
  ar->allocation_size = size;
  ar->arow = arow;
  //record_underlying_hooks(); // not sure why example re-saves hooks here

  // do our work (outside of hookland)
  //printf("malloc_hook sees size %lx from %p; returns %p\n", size, caller, result);
  arow->total_allocation_count += 1;
  arow->open_allocation_count += 1;
  arow->total_allocation_bytes += size;
  arow->open_allocation_bytes += size;

  install_hooks();

  return result;
}

void free_hook(void* ptr, const void *caller) {
  if (ptr==NULL) {
    // Glad I could help!
    return;
  }

  remove_hooks();

  // do our work (outside of hookland)
  AccountingHeader* ar = (AccountingHeader*)((char*) ptr - sizeof(AccountingHeader));
  void* orig_ptr;
  if (ar->magic != ACCOUNTING_MAGIC) {
    // Uh, that's not mine.
    // https://getyarn.io/yarn-clip/00a2eaf9-a18d-4aea-b600-6e4b19bbe4d1
    orig_ptr = ptr;
    printf("free_hook frees someone else's ptr %p\n", ptr);
  } else {
    orig_ptr = ar;
//    printf("free_hook sees free %p size %lx from %p\n", ptr, ar->allocation_size, caller);

    ARow* arow = ar->arow;
    arow->open_allocation_count -= 1;
    arow->open_allocation_bytes -= ar->allocation_size;
  }

  free(orig_ptr);

  install_hooks();
}

void init_malloc_accounting() {
  malloc_accounting_default_scope();
  record_underlying_hooks();
  install_hooks();
}

void fini_malloc_accounting() {
    atable.display();
}

void malloc_accounting_set_scope(const char* scope, const char* subscope) {
  atable.set_active_label(Label(scope, subscope));
}

void malloc_accounting_set_scope(const char* scope) {
  malloc_accounting_set_scope(scope, "");
}

void malloc_accounting_default_scope() {
  atable.clear_active_label();
}
#else // MALLOC_ACCOUNTING
// implementations are empty inlines in .h
#endif // MALLOC_ACCOUNTING
