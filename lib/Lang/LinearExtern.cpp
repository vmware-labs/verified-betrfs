#include "LinearExtern.h"


namespace LinearExtern {

////////////////////////////////////////////////////////////
//
//   Ints (for testing purposes)
//
////////////////////////////////////////////////////////////

uint64 MakeLinearInt(uint64 u) { return u; }
void DiscardLinearInt(uint64 u) { (void) u; }

////////////////////////////////////////////////////////////
//
//   Linear sequences
//
////////////////////////////////////////////////////////////

template <typename A>
using linear_seq = std::vector<A>*;

template <typename A>
using shared_seq = linear_seq<A>;

template <typename A>
A seq_get(linear_seq<A> s, uint64 i) {
  return (*s)[i];
}

template <typename A>
linear_seq<A> seq_set(linear_seq<A> s, uint64 i, A a) {
  (*s)[i] = a;
  return s;
}

template <typename A>
uint64 seq_length(linear_seq<A> s) {
  return s->size();
}

template <typename A>
linear_seq<A> seq_empty() {
  linear_seq<A> ret = new std::vector<A>;
  return ret;
}

template <typename A>
linear_seq<A> seq_alloc(uint64 length, A a) {
  linear_seq<A> ret = new std::vector<A>;
  ret->assign(length, a);
  return ret;
}

template <typename A>
Tuple0 seq_free(linear_seq<A> s) {
  s->clear();
  delete s;
  Tuple0 ret;
  return ret;
}

template <typename A>
DafnySequence<A> seq_unleash(linear_seq<A> s) {
  DafnySequence<A> ret(*s);  // TODO: Copies contents of s into ret
  seq_free(*s);
  return ret;
}

template <typename A>
Tuple0 seq_length_bound(DafnySequence<A> s) {
  return Tuple0();
}

template <typename A>
Tuple0 shared_seq_length_bound(linear_seq<A> s) {
  return Tuple0();
}

/* TODO
template <typename A>
shared_seq<A> share_seq(struct as__linear<DafnySequence<A>> a) {
  return 
}
*/

template <typename A>
linear_seq<A> TrustedRuntimeSeqResize(linear_seq<A> s, uint64 newlen) {
  s->resize(newlen);
  return s;
}

////////////////////////////////////////////////////////////
//
//   lseqs
//
////////////////////////////////////////////////////////////
template <typename A>
using lseq = std::vector<LinearMaybe::maybe<A>>*;

template <typename A>
uint64 lseq_length_raw(lseq<A> s) {
  return s->size();
}

template <typename A>
lseq<A> lseq_alloc_raw(uint64 length) {
  lseq<A> ret;
  ret = new std::vector<LinearMaybe::maybe<A>>;
  ret->assign(length, get_default<LinearMaybe::maybe<A>>::call());
  return ret;
}

template <typename A>
Tuple0 lseq_free_raw(lseq<A> s) {
  s->clear();
  delete s;
  Tuple0 ret;
  return ret;
}

template <typename A>
Tuple2<lseq<A>, LinearMaybe::maybe<A>> lseq_swap_raw_fun(lseq<A> s1, uint64 i, LinearMaybe::maybe<A> a1) {
  LinearMaybe::maybe<A> oldElement = (*s1)[i];
  (*s1)[i] = a1;
  Tuple2 ret(s1, oldElement);
  return ret;
}

template <typename A>
LinearMaybe::maybe<A> lseq_share_raw(lseq<A> s, uint64 i) {
  return (*s)[i];
}

template <typename A>
lseq<A> TrustedRuntimeLSeqResize(lseq<A> s, uint64 newlen) {
  s->resize(newlen);
  return s;
}

template <typename A>
lseq<A> get_lseq_default() {
  lseq<A> ret;
  return ret;
}

template <typename A>
Tuple0 lseq_length_bound(lseq<A> s) {
  return Tuple0();
}

}

//template<typename A>
//struct std::hash<LinearExtern::linear_seq<A>> {
//  std::size_t operator()(const LinearExtern::linear_seq<A>& x) const {
//    size_t seed = 0;
//    for (size_t i = 0; i < x.size(); i++) {      
//      hash_combine<U>(seed, x[i]);
//    }
//    return seed;
//  }
//};
//
//template<typename A>
//struct std::hash<LinearExtern::shared_seq<A>> {
//  std::size_t operator()(const LinearExtern::shared_seq<A>& x) const {
//    size_t seed = 0;
//    for (size_t i = 0; i < x.size(); i++) {      
//      hash_combine<U>(seed, x[i]);
//    }
//    return seed;
//  }
//};
//
//template<typename A>
//struct std::hash<LinearExtern::lseq<A>> {
//  std::size_t operator()(const LinearExtern::lseq<A>& x) const {
//    size_t seed = 0;
//    for (size_t i = 0; i < x.size(); i++) {      
//      hash_combine<U>(seed, x[i]);
//    }
//    return seed;
//  }
//};
