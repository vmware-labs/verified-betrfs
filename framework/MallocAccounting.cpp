#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <malloc.h>
#include <assert.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <unordered_map>
#include <vector>

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

bool cstr_ends_with(const char* haystack, const char* needle) {
  int haystack_len = strlen(haystack);
  int needle_len = strlen(needle);
  if (haystack_len < needle_len) { return false; }
  return strcmp(&haystack[haystack_len - needle_len], needle) == 0;
}

// OS view of heap size
size_t external_heap_size() {
  size_t result = -1;
  FILE* fp = fopen("/proc/self/maps", "r");
  while (true) {
    char space[1000];
    char* line = fgets(space, sizeof(space), fp);
    if (line==NULL) { break; }
    if (cstr_ends_with(line, "[heap]\n")) {
      char* remainder;
      long base = strtol(line, &remainder, 16);
      long end = strtol(&remainder[1], NULL, 16);
      result = end - base;
      break;
    }
  }
  fclose(fp);
  return result;
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
  Label() {
    scope = NULL;
    subscope = NULL;
  }
  bool equals(const Label& other) const {
    return strcmp(scope, other.scope) == 0
      && strcmp(subscope, other.subscope) == 0;
  }
  bool operator==(const Label& other) const {
    return scope==other.scope && subscope==other.subscope;
  }
};

namespace std {
  template<> struct hash<Label> {
    std::size_t operator()(const Label& label) const {
      //return hashCstr(label.scope) & hashCstr(label.subscope);
      // Actually, I think I'm willing to assume that the Label fields
      // are interned, so we only have to look at the pointers.
      return ((size_t) label.scope)*193 ^ ((size_t)label.subscope);
    }
  };
}

struct ARow {
  Label label;
  uint64_t total_allocation_count;
  uint64_t open_allocation_count;
  uint64_t total_allocation_bytes;
  uint64_t open_allocation_bytes;
  ARow(const Label &label)
    : label(label),
      total_allocation_count(0),
      open_allocation_count(0),
      total_allocation_bytes(0),
      open_allocation_bytes(0)
  {}
};

// Somebody wishes he had a hashtable, doesn't somebody?
Label g_default_label("default", "");
class ATable {
private:
  std::unordered_map<Label, ARow> umap;
  Label g_active_label;

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
  size_t total_open();  // total open allocation bytes
};

ATable::ATable() {
  g_active_label = g_default_label;
}

ARow* ATable::get_or_add_row(const Label& label) {
  assert(label.scope != NULL);
  auto insertPair = umap.emplace(label, ARow(label));
  // Don't care if insert succeeded or was just a lookup; just want
  // the row.
  return &insertPair.first->second;
}

size_t ATable::total_open() {
  size_t total = 0;
  for (auto it = umap.begin(); it != umap.end(); it++)  {
    total += it->second.open_allocation_bytes;
  }
  return total;
}

void ATable::display() {
  Label totalLabel("total", "");
  ARow total(totalLabel);
  printf("%10s %10s %10s %10s  %s\n",
    "tot cnt", "open cnt", "tot byt", "open byt", "label");
  printf("%10s %10s %10s %10s  %s\n",
    "-------", "--------", "-------", "--------", "----------");
  std::vector<ARow> rows;
  for (auto it = umap.begin(); it != umap.end(); it++)  {
    rows.push_back(it->second);
  }

  sort(rows.begin(), rows.end(), [](const ARow& lhs, const ARow& rhs) {
      return lhs.open_allocation_bytes < rhs.open_allocation_bytes;
  });

  for (auto it = rows.begin(); it != rows.end(); it++)  {
    ARow* row = &(*it);
    Label* label = &row->label;
    printf("%10ld %10ld %10ld %10ld  %s.%s\n",
      row->total_allocation_count,
      row->open_allocation_count,
      row->total_allocation_bytes,
      row->open_allocation_bytes,
      label->subscope,
      label->scope);
    total.total_allocation_count += row->total_allocation_count;
    total.open_allocation_count += row->open_allocation_count;
    total.total_allocation_bytes += row->total_allocation_bytes;
    total.open_allocation_bytes += row->open_allocation_bytes;
  }
  printf("%10s %10s %10s %10s  %s\n",
    "-------", "--------", "-------", "--------", "----------");
  printf("%10ld %10ld %10ld %10ld  %s.%s\n",
    total.total_allocation_count,
    total.open_allocation_count,
    total.total_allocation_bytes,
    total.open_allocation_bytes,
    "total",
    "");
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

    // This occurs due to allocations that happened before our hook
    // mechanism got installed. Not very interesting. 
    //printf("free_hook frees someone else's ptr %p\n", ptr);
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

void dump_proc_self_maps() {
  // copy /proc/self/maps to stdout
  // to confirm that the heap is all that matters.
  FILE* fp = fopen("/proc/self/maps", "r");
  while (true) {
    char space[1000];
    char* line = fgets(space, sizeof(space), fp);
    if (line==NULL) { break; }
    fputs(line, stdout);
  }
  fclose(fp);
}

void malloc_accounting_display(const char* label) {
  printf("*** Malloc accounting at %s\n", label);
  atable.display();
  // dump_proc_self_maps();
}

void fini_malloc_accounting() {
  malloc_accounting_display("fini");
}

// This is here to confirm that malloc accounting indeed finds
// all of the memory that the OS is giving us. When I studied this,
// I found that the OS heap accounting was about 20% more than what
// we used in malloc -- probably fragmentation. It stayed fairly
// proportional, giving me confidence that malloc is gettingt a
// complete view.
// (Note that there could also be other ways to gobble process memory,
// like mmap, but we're not doing that; /proc/maps only shows
// text segments and other ordinary features.)
// Finally, we could also be gobbling up other cgroup-y memory -- maybe
// space in the buffer cache? Not worrying about that here.
void malloc_accounting_status() {
  printf("proc-heap %8ld malloc-accounting-total %8ld\n",
    external_heap_size(),
    atable.total_open());
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
