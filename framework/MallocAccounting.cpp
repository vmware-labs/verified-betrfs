#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unordered_map>
#include <vector>

#include "MallocAccounting.h"

#if MALLOC_ACCOUNTING

#include <malloc.h>

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
void external_heap_size(size_t* heap, size_t* all_maps) {
  size_t result = -1;
  FILE* fp = fopen("/proc/self/maps", "r");
  size_t total = 0;
  while (true) {
    char space[1000];
    char* line = fgets(space, sizeof(space), fp);
    if (line==NULL) { break; }
    char* remainder;
    size_t base = strtol(line, &remainder, 16);
    size_t end = strtol(&remainder[1], NULL, 16);
    result = end - base;
    total += result;

    if (cstr_ends_with(line, "[heap]\n")) {
      *heap = result;
    }
  }
  fclose(fp);
  *all_maps = total;
}
  
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

// A little header we prepend to each allocation so we can track the
// allocation size so we know what to free later.
#define ACCOUNTING_MAGIC 0x1badf00f
typedef struct {
  uint64_t magic; // identify my own mallocs
  size_t allocation_size;
  Label label;
} AccountingHeader;

struct ARow {
  Label label;
  uint64_t total_count;
  uint64_t open_count;
  uint64_t total_bytes;
  uint64_t open_bytes;
  ARow(const Label& label)
    : label(label),
      total_count(0),
      open_count(0),
      total_bytes(0),
      open_bytes(0)
  {}

  inline void record_allocate(size_t size) {
    total_count += 1;
    open_count += 1;
    total_bytes += size;
    open_bytes += size;
  }

  inline void record_free(size_t size) {
    open_count -= 1;
    open_bytes -= size;
  }

#define AROW_BUFSIZE (1024)
  static char* display_header(char* buf, int bufsize) {
    assert(bufsize==AROW_BUFSIZE);
    snprintf(buf, bufsize, "%14s %14s %14s %14s  %s",
      "tot cnt", "open cnt", "tot byt", "open byt", "label");
    return buf;
  }

  char* display(char* buf, int bufsize) {
    assert(bufsize==AROW_BUFSIZE);
    snprintf(buf, bufsize, "%14ld %14ld %14ld %14ld %s.%s",
      total_count,
      open_count,
      total_bytes,
      open_bytes,
      label.subscope,
      label.scope);
    return buf;
  }
};

//////////////////////////////////////////////////////////////////////////////
// Scope Map
//
// Label allocations with the call site that caused them, to find leaks.
// "scopes" are Labels given by the emitted code (or framework code)
// that are high enough up the call graph that they are interpretable.

Label g_default_label("default", "");

class ScopeMap {
private:
  std::unordered_map<Label, ARow> umap;
  Label g_active_label;

public:
  ScopeMap();

  void set_active_label(const Label& label) {
    assert(g_active_label.equals(g_default_label)); // nested label calls; need label stack?
    g_active_label = label;
  }
  void clear_active_label() { g_active_label = g_default_label; }

  // Add a row to the table if it's absent.
  ARow* get_or_add_row(const Label& label);

  ARow* get_active_row() { return get_or_add_row(g_active_label); }
  
  void display();

  inline const Label* get_active_label() { return &g_active_label; }

  inline void record_allocate(size_t size) {
#if MALLOC_ACCOUNTING_ENABLE_SCOPES
    ARow* arow = get_active_row();
    arow->record_allocate(size);
#endif // MALLOC_ACCOUNTING_ENABLE_SCOPES
  };

  inline void record_free(const Label& label, size_t size) {
#if MALLOC_ACCOUNTING_ENABLE_SCOPES
    ARow* arow = get_or_add_row(label);
    arow->record_free(size);
#endif // MALLOC_ACCOUNTING_ENABLE_SCOPES
  }
};

ARow* ScopeMap::get_or_add_row(const Label& label) {
  assert(label.scope != NULL);
  auto insertPair = umap.emplace(label, ARow(label));
  // Don't care if insert succeeded or was just a lookup; just want
  // the row.
  return &insertPair.first->second;
}

ScopeMap::ScopeMap() {
  g_active_label = g_default_label;
}

void ScopeMap::display() {
#if !MALLOC_ACCOUNTING_ENABLE_SCOPES
  return;
#endif // MALLOC_ACCOUNTING_ENABLE_SCOPES
  char buf[AROW_BUFSIZE];
  printf("ma-hdr   %s\n", ARow::display_header(buf, sizeof(buf)));
  printf("ma-hdr   ----------------------------------------------------  ----------\n");
  std::vector<ARow> rows;
  for (auto it = umap.begin(); it != umap.end(); it++)  {
    rows.push_back(it->second);
  }

  sort(rows.begin(), rows.end(), [](const ARow& lhs, const ARow& rhs) {
      return lhs.open_bytes < rhs.open_bytes;
  });

  for (auto it = rows.begin(); it != rows.end(); it++)  {
    ARow* row = &(*it);
    printf("ma-scope %s\n",
      row->display(buf, sizeof(buf)));
  }
}

//////////////////////////////////////////////////////////////////////////////
// A pattern-matcher for chasing down particular allocations

struct Microscope {
  uint64_t min_size;
  uint64_t max_size;
  ARow arow;
  const char* description;
};

static const char* match_any = "any";

Microscope microscopes[] = {
  // row 0 is reserved for total
  {0, ULLONG_MAX, ARow(Label(match_any, "")), "total"},
  {0, (1<<20)-1, ARow(Label(match_any, "")), "coarse-small"},
  {1<<20, ULLONG_MAX, ARow(Label(match_any, "")), "coarse-large"},
  {0, 511, ARow(Label("[T = unsigned char]", "explicit-seq")), "es511"},
  {512, 512, ARow(Label("[T = unsigned char]", "explicit-seq")), "es512"},
  {513, (1<<20)-1, ARow(Label("[T = unsigned char]", "explicit-seq")), "esMid"},
  {1<<20, ULLONG_MAX, ARow(Label("[T = unsigned char]", "explicit-seq")), "esLarge"},
  {0, 511, ARow(Label("[T = unsigned char]", "seq-from-array")), "sfa511"},
  {512, 512, ARow(Label("[T = unsigned char]", "seq-from-array")), "sfa512"},
  {513, (1<<20)-1, ARow(Label("[T = unsigned char]", "seq-from-array")), "sfaMid"},
  {1<<20, ULLONG_MAX, ARow(Label("[T = unsigned char]", "seq-from-array")), "sfaLarge"},
};

class MicroscopeBench {
public:
  inline void record_allocate(const Label& label, size_t size) {
#if MALLOC_ACCOUNTING_ENABLE_SCOPES
    for (unsigned int i=0; i<sizeof(microscopes)/sizeof(Microscope); i++) {
      Microscope& microscope = microscopes[i];
      if (microscope.min_size <= size
          && size <= microscope.max_size
          && (microscope.arow.label.scope == match_any
            || microscope.arow.label.equals(label))) {
        microscope.arow.record_allocate(size);
      }
    }
#endif // MALLOC_ACCOUNTING_ENABLE_SCOPES
  }

  inline void record_free(const Label& label, size_t size) {
#if MALLOC_ACCOUNTING_ENABLE_SCOPES
    for (unsigned int i=0; i<sizeof(microscopes)/sizeof(Microscope); i++) {
      Microscope& microscope = microscopes[i];
      if (microscope.min_size <= size
          && size <= microscope.max_size
          && (microscope.arow.label.scope == match_any
            || microscope.arow.label.equals(label))) {
        microscope.arow.record_free(size);
      }
    }
#endif // MALLOC_ACCOUNTING_ENABLE_SCOPES
  }

  void display() {
    for (unsigned int i=0; i<sizeof(microscopes)/sizeof(Microscope); i++) {
      Microscope& microscope = microscopes[i];
      char buf[AROW_BUFSIZE];
      printf("ma-microscope %s %s\n",
        microscope.arow.display(buf, sizeof(buf)), microscope.description);
    }
  }
};

//////////////////////////////////////////////////////////////////////////////
// Fine-grained histogram

class FineHistogram {
private:
  std::unordered_map<size_t, size_t> histogram;

  void histogram_increment(size_t size, int delta);

public:
  inline void record_allocate(size_t size) {
#if MALLOC_ACCOUNTING_ENABLE_FULL_HISTOGRAM
    histogram_increment(size, 1);
#endif // MALLOC_ACCOUNTING_ENABLE_FULL_HISTOGRAM
  }

  inline void record_free(size_t size) {
#if MALLOC_ACCOUNTING_ENABLE_FULL_HISTOGRAM
    histogram_increment(size, -1);
#endif // MALLOC_ACCOUNTING_ENABLE_FULL_HISTOGRAM
  }

  void display();
};

void FineHistogram::histogram_increment(size_t size, int delta) {
  auto insertPair = histogram.emplace(size, 0);
  auto eltIt = insertPair.first;
  auto kvPointer = &(*eltIt);
  kvPointer->second += delta;
}

void FineHistogram::display() {
#if !MALLOC_ACCOUNTING_ENABLE_FULL_HISTOGRAM
  return; // nothing to display.
#endif // MALLOC_ACCOUNTING_ENABLE_FULL_HISTOGRAM
  std::vector<std::pair<size_t, size_t>> buckets;
  for (auto it = histogram.begin(); it != histogram.end(); it++)  {
    buckets.push_back(std::pair<size_t, size_t>(it->first, it->second));
  }
  sort(buckets.begin(), buckets.end(), [](const std::pair<size_t,size_t>& lhs, const std::pair<size_t,size_t>& rhs) {
      return lhs.first < rhs.first;
  });

  size_t total = 0;
  printf("ma-fine-histogram {");
  for (auto it = buckets.begin(); it != buckets.end(); it++)  {
    auto pair = *it;
    total += pair.first * pair.second;
    printf("%ld:%ld,", pair.first, pair.second);
  }
  printf("}\n");
  printf("ma-fine-histogram-total %ld\n", total);
}

//////////////////////////////////////////////////////////////////////////////
// table of interesting metrics.

class ATable {
public:
  // These different modules are activated/deactivated with #defines in .h
  ScopeMap scope_map;
  FineHistogram fine_histogram;
  MicroscopeBench microscope_bench;

  inline const Label* record_allocate(size_t size) {
    const Label* label = scope_map.get_active_label();
    fine_histogram.record_allocate(size);
    scope_map.record_allocate(size);
    microscope_bench.record_allocate(*label, size);
    return label; // tuck into allocation header so we know it at free time
  }

  // scope_row is tucked into allocation to avoid a hash lookup at free time
  inline void record_free(size_t size, const Label& label) {
    fine_histogram.record_free(size);
    scope_map.record_free(label, size);
    microscope_bench.record_free(label, size);
  }

  size_t total_open_bytes() {
    // row 0 is reserved for total
    return microscopes[0].arow.open_bytes;
  }
};

ATable atable;

//////////////////////////////////////////////////////////////////////////////

// If enabled, allocations bigger than MMAP_POOL_SIZE are done with mmap
#define MMAP_POOL_ENABLE 0
#define MMAP_POOL_SIZE_THRESH (1<<20) /* 1MB */

void *malloc_hook(size_t size, const void *caller) {
  void *underlying;
  void *result;

  remove_hooks();
  // do our work (outside of hookland)

  size_t underlying_size = size + sizeof(AccountingHeader);

  // Call real malloc
  bool use_mmap = MMAP_POOL_ENABLE && (size >= MMAP_POOL_SIZE_THRESH);
  if (use_mmap) {
    underlying = mmap(NULL, underlying_size, PROT_READ|PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
  } else {
    underlying = malloc(underlying_size);
  }

  AccountingHeader* ar = (AccountingHeader*) underlying;
  result = (char*) underlying + sizeof(AccountingHeader);
  ar->magic = ACCOUNTING_MAGIC;
  ar->allocation_size = size;
  ar->label = *atable.record_allocate(size);

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
  size_t size = 0;
  bool use_munmap;

  if (ar->magic != ACCOUNTING_MAGIC) {
    // That's, uh, not mine.
    // https://getyarn.io/yarn-clip/00a2eaf9-a18d-4aea-b600-6e4b19bbe4d1
    orig_ptr = ptr;

    // This occurs due to allocations that happened before our hook
    // mechanism got installed. Not very interesting. 
    //printf("free_hook frees someone else's ptr %p\n", ptr);
    use_munmap = false;
  } else {
    orig_ptr = ar;
//    printf("free_hook sees free %p size %lx from %p\n", ptr, ar->allocation_size, caller);

    size = ar->allocation_size;
    atable.record_free(size, ar->label);
    use_munmap = MMAP_POOL_ENABLE && (size >= MMAP_POOL_SIZE_THRESH);
  }

  if (use_munmap) {
    size_t underlying_size = size + sizeof(AccountingHeader);
//    printf("--munmap big block %.1fMB\n", underlying_size/(1024*1024.0));
    munmap(orig_ptr, underlying_size);
  } else {
    free(orig_ptr);
  }

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
  printf("ma-display-header %s\n", label);
  atable.scope_map.display();
  atable.fine_histogram.display();
  atable.microscope_bench.display();
  // dump_proc_self_maps();
  // atable.display_histogram();
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
  size_t heap, all_maps;
  external_heap_size(&heap, &all_maps);
  printf("os-map-total %8ld os-map-heap %8ld malloc-accounting-total %8ld\n",
    all_maps,
    heap,
    atable.total_open_bytes());
}

#if MALLOC_ACCOUNTING_ENABLE_SCOPES
void malloc_accounting_set_scope(const char* scope, const char* subscope) {
  atable.scope_map.set_active_label(Label(scope, subscope));
}

void malloc_accounting_set_scope(const char* scope) {
  malloc_accounting_set_scope(scope, "");
}

void malloc_accounting_default_scope() {
  atable.scope_map.clear_active_label();
}
#endif // MALLOC_ACCOUNTING_ENABLE_SCOPES
#else // MALLOC_ACCOUNTING
// implementations are empty inlines in .h
#endif // MALLOC_ACCOUNTING

const char* horrible_amass_label = NULL;
