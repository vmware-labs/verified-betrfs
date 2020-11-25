#pragma once

#include <functional>
#include "DafnyRuntime.h"

namespace LinearBox_s {

  template<typename A>
  struct DestructorFunction {
    std::function<Tuple0(A)> f;
  };

  template <typename A>
  class SwapAffine {
    public:
      SwapAffine(A a) {
        this-> a = a;
      }

      A Swap(A a1) {
        A ret = this->a;
        this->a = a1;
        return ret;
      }

      A Borrow() { 
        return a;
      }
    private:
      A a;
  };

  template <typename A>
  class SwapLinear {
    public:
      SwapLinear(A a, DestructorFunction<A> d) {
        this-> a = a;
        this-> d = d;
      }

      A Swap(A a1) {
        A ret = this->a;
        this->a = a1;
        return ret;
      }

      A Borrow() { 
        return a;
      }

      ~SwapLinear() {
        d.f(a);
      }
    private:
      A a;
      DestructorFunction<A> d;
  };

  template<typename A>
  DestructorFunction<A> ToDestructor(Tuple0 (*f)(A)) {
    struct DestructorFunction<A> df;
    df.f = f;
    return df;
  }

  template<typename A, typename E>
  DestructorFunction<A> ToDestructorEnv(Tuple0 (*f)(A, E), E e) {
    struct DestructorFunction<A> df;
    df.f = [=](A a) {return f(a, e);};
    return df;
  }

  template<typename A>
  Tuple0 CallDestructor(DestructorFunction<A> d, A a) {
    return d.f(a);
  }

}
