#pragma once

#include "DafnyRuntime.h"

namespace LinearBox_s {

  template <typename A>
  class SwapLinear {
    public:
      SwapLinear(A a) {
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

}
