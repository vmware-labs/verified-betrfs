// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#pragma once

#include "DafnyRuntime.h"

#include <vector>
#include <assert.h>

namespace LinearMaybe {
////////////////////////////////////////////////////////////
//
//   Maybe
//
////////////////////////////////////////////////////////////

template <typename A>
struct maybe {
  A a;
};

// This is required, because lseqs are compiled as std::vector's of
// maybes, and hence the automatic, compiler-generated equality on
// lseqs requires an equality on maybe's.  However, this operator
// is not currently accessible from Dafny
template <typename A>
bool operator==(const maybe<A> &left, const maybe<A> &right) {
  assert(false);  // Unsafe to hit this at runtime
  return left.a == right.a;
}

template <typename A>
A* peek(maybe<A>& m) { return &m.a; }

template <typename A>
A unwrap(maybe<A> m) { return m.a; }

template <typename A>
maybe<A> give(A a) { 
  struct maybe<A> m;
  m.a = a;
  return m;
}

template <typename A>
//maybe<A> empty() { return maybe(get_default<A>::call()); }
maybe<A> empty() { 
  struct maybe<A> m;
  return m;  // REVIEW: Safe, b/c !has ?
}    

template <typename A>
Tuple0 discard(maybe<A> m) { (void)m; Tuple0 ret; return ret; } 

}

template<typename A>
struct get_default<LinearMaybe::maybe<A>> {
  static LinearMaybe::maybe<A> call() { 
    struct LinearMaybe::maybe<A> m;
    m.a = get_default<A>::call();
    return m; 
  }
};

template<typename A>
struct std::hash<LinearMaybe::maybe<A>> {
  std::size_t operator()(const LinearMaybe::maybe<A>& x) const {
    size_t seed = 0;
    hash_combine<A>(seed, x.a);
    return seed;
  }
};

namespace LinearExtern {

////////////////////////////////////////////////////////////
//
//   Ints (for testing purposes)
//
////////////////////////////////////////////////////////////

uint64 MakeLinearInt(uint64 u);
void DiscardLinearInt(uint64 u);

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
  seq_free(s);
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
struct LinearLSeq {
  size_t len;
  LinearMaybe::maybe<A>* ptr;
};

template <typename A>
bool operator==(const LinearLSeq<A> &left, const LinearLSeq<A> &right) {
  std::cerr << "Error: LinearLSeq == called" << std::endl;
  exit(1);
}

template <typename A>
using lseq = LinearLSeq<A>;

template <typename A>
uint64 lseq_length_raw(lseq<A> s) {
  return s.len;
}

template <typename A>
lseq<A> lseq_alloc_raw(uint64 length) {
  lseq<A> ret;
  ret.ptr = new LinearMaybe::maybe<A>[length];
  ret.len = length;
  return ret;
}

template <typename A>
Tuple0 lseq_free_raw(lseq<A> s) {
  delete[] s.ptr;
  Tuple0 ret;
  return ret;
}

template <typename A>
Tuple<lseq<A>, LinearMaybe::maybe<A>> lseq_swap_raw_fun(lseq<A> s1, uint64 i, LinearMaybe::maybe<A> a1) {
  LinearMaybe::maybe<A> oldElement = s1.ptr[i];
  s1.ptr[i] = a1;
  Tuple ret(s1, oldElement);
  return ret;
}

template <typename A>
LinearMaybe::maybe<A>* lseq_share_raw(lseq<A> s, uint64 i) {
  return &s.ptr[i];
}

template <typename A>
lseq<A> TrustedRuntimeLSeqResize(lseq<A> s, uint64 newlen) {
  std::cerr << "Error: lseq resize not implemented" << std::endl;
  exit(1);
  /*
  s->resize(newlen);
  return s;
  */
}

template <typename A>
lseq<A> get_lseq_default() {
  return LinearLSeq<A>();
}

template <typename A>
Tuple0 lseq_length_bound(lseq<A> s) {
  return Tuple0();
}

}

template<typename A>
struct std::hash<LinearExtern::LinearLSeq<A>> {
  std::size_t operator()(const LinearExtern::LinearLSeq<A>& x) const {
    std::cerr << "Error: lseq hash called" << std::endl;
    exit(1);
  }
};


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
