#pragma once

#include <memory>
#include <string>

#define MALLOC_ACCOUNTING_ENABLE_SCOPES 1
#define MALLOC_ACCOUNTING_ENABLE_FULL_HISTOGRAM 0

#if MALLOC_ACCOUNTING
void init_malloc_accounting();
void malloc_accounting_status();  // short status comparing tot bytes to proc maps heap
void malloc_accounting_display(const char* label); // full accountingg
void fini_malloc_accounting();
#else // MALLOC_ACCOUNTING
inline void init_malloc_accounting() {}
inline void malloc_accounting_status() {}
inline void malloc_accounting_display(const char* label) {}
inline void fini_malloc_accounting() {}
// You don't need scopes if you've turned off the main MALLOC_ACCOUNTING knob.
#undef MALLOC_ACCOUNTING_ENABLE_SCOPES
#define MALLOC_ACCOUNTING_ENABLE_SCOPES 0
#endif // MALLOC_ACCOUNTING

#if MALLOC_ACCOUNTING_ENABLE_SCOPES
void malloc_accounting_set_scope(const char* scope);
void malloc_accounting_set_scope(const char* scope, const char* subscope);
void malloc_accounting_default_scope();
template<typename T> char const* malloc_accounting_get_type_name() {
  // truncate "const char *malloc_accounting_get_type_name() " prefix
  return &__PRETTY_FUNCTION__[46];
}
#else // MALLOC_ACCOUNTING_ENABLE_SCOPES
inline void malloc_accounting_set_scope(const char* scope) {}
inline void malloc_accounting_set_scope(const char* scope, const char* subscope) {}
inline void malloc_accounting_default_scope() {}
template<typename T> inline char const* malloc_accounting_get_type_name() {
  return "";  // gets optimized out, I'd hope, since it's only used as an arg to the empty routines above.
}
#endif // MALLOC_ACCOUNTING_ENABLE_SCOPES

template< typename T, typename... Args >
  inline std::shared_ptr<T>
  malloc_accounting_make_shared( const char* scope, Args&&... args )
  {
    malloc_accounting_set_scope(scope);
    auto ptr = std::make_shared<T>(std::forward<Args>(args)...);
    malloc_accounting_default_scope();
    return ptr;
  }

// Convert a string to std::string, which involves an allocation (which we then
// label).
inline std::string malloc_accounting_std_string(const char* c_str) {
  malloc_accounting_set_scope("std_string");
  std::string std_string(c_str);
  malloc_accounting_default_scope();
  return std_string;
}

extern const char* horrible_amass_label;
