#include <atomic>

namespace Atomics {


template <typename V>
struct InternalAtomic {
  std::atomic<V>* slot;
};

template <typename V, typename G>
InternalAtomic<V> new__atomic(V v) {
  InternalAtomic<V> ia;
  ia.slot = new std::atomic<V>(v);
  return ia;
}

template <typename V, typename G>
bool execute__atomic__compare__and__set__strong(
    InternalAtomic<V> a,
    V v1,
    V v2)
{
  return a.slot->compare_exchange_strong(v1, v2, std::memory_order_seq_cst);
}

template <typename V, typename G>
bool execute__atomic__compare__and__set__weak(
    InternalAtomic<V> a,
    V v1,
    V v2)
{
  return a.slot->compare_exchange_weak(v1, v2, std::memory_order_seq_cst);
}

template <typename V, typename G>
V execute__atomic__load(
    InternalAtomic<V> a)
{
  return a.slot->load(std::memory_order_seq_cst);
}

template <typename V, typename G>
void execute__atomic__store(
    InternalAtomic<V> a,
    V v)
{
  a.slot->store(v, std::memory_order_seq_cst);
}

template <typename V, typename G>
V execute__atomic__fetch__or(
    InternalAtomic<V> a,
    V v)
{
  return a.slot->fetch_or(v, std::memory_order_seq_cst);
}

template <typename V, typename G>
V execute__atomic__fetch__and(
    InternalAtomic<V> a,
    V v)
{
  return a.slot->fetch_and(v, std::memory_order_seq_cst);
}

template <typename V, typename G>
V execute__atomic__fetch__xor(
    InternalAtomic<V> a,
    V v)
{
  return a.slot->fetch_xor(v, std::memory_order_seq_cst);
}

template <typename V, typename G>
V execute__atomic__fetch__add(
    InternalAtomic<V> a,
    V v)
{
  return a.slot->fetch_add(v, std::memory_order_seq_cst);
}

template <typename V, typename G>
V execute__atomic__fetch__sub(
    InternalAtomic<V> a,
    V v)
{
  return a.slot->fetch_sub(v, std::memory_order_seq_cst);
}

// Dafny doesn't have generics over numeric types
// so we have to define the arithmetic actions
// over all integer precisions individually,
// e.g., execute__atomic__fetch__sub__uint8

#define ARITH_SPECIALIZE(t, name) \
  template<typename G> \
  t execute__atomic__fetch__sub__ ## name (InternalAtomic<t> a, t v) { \
      return execute__atomic__fetch__sub<t, G>(a, v); } \
      \
  template<typename G> \
  t execute__atomic__fetch__add__ ## name (InternalAtomic<t> a, t v) { \
      return execute__atomic__fetch__add<t, G>(a, v); } \
      \
  template<typename G> \
  t execute__atomic__fetch__or__ ## name (InternalAtomic<t> a, t v) { \
      return execute__atomic__fetch__or<t, G>(a, v); } \
      \
  template<typename G> \
  t execute__atomic__fetch__xor__ ## name (InternalAtomic<t> a, t v) { \
      return execute__atomic__fetch__xor<t, G>(a, v); } \
      \
  template<typename G> \
  t execute__atomic__fetch__and__ ## name (InternalAtomic<t> a, t v) { \
      return execute__atomic__fetch__and<t, G>(a, v); } \

ARITH_SPECIALIZE(uint8_t, uint8)
ARITH_SPECIALIZE(uint16_t, uint16)
ARITH_SPECIALIZE(uint32_t, uint32)
ARITH_SPECIALIZE(uint64_t, uint64)

template <typename V, typename G>
void execute__atomic__noop(
    InternalAtomic<V> _a)
{
  // do nothing
}

static_assert(std::atomic<uint8_t>::is_always_lock_free);
static_assert(std::atomic<uint16_t>::is_always_lock_free);
static_assert(std::atomic<uint32_t>::is_always_lock_free);
static_assert(std::atomic<uint64_t>::is_always_lock_free);

template <typename V, typename G>
using Atomic = InternalAtomic<V>;

}
