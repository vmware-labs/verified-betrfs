#pragma once

#include <memory>
#include <string>

// TODO switcha all this stuff off with macros (or inline empty methods)
void init_malloc_accounting();
void fini_malloc_accounting();
void malloc_accounting_set_scope(const char* scope);
void malloc_accounting_set_scope(const char* scope, const char* subscope);
void malloc_accounting_default_scope();

template<typename T> char const* malloc_accounting_get_type_name() {
  // truncate "const char *malloc_accounting_get_type_name() " prefix
  return &__PRETTY_FUNCTION__[46];
}

template< typename T, typename... Args >
  std::shared_ptr<T>
  malloc_accounting_make_shared( const char* scope, Args&&... args )
  {
    malloc_accounting_set_scope(scope);
    auto ptr = std::make_shared<T>(std::forward<Args>(args)...);
    malloc_accounting_default_scope();
    return ptr;
  }

std::string malloc_accounting_std_string(const char* c_str);
