// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#pragma once

namespace LinearRegion {
  typedef struct {
    // Empty placeholder since NewRegion and FreeRegion are no-ops
  } Region;
}

namespace LinearRegionId_s {
  // We don't define RegionId type, since the only places it is used
  // are ghost
}

namespace LinearRegionRefCell_s {
  template <typename A>
  using RefCell = std::shared_ptr<A>;
}

namespace LinearRegionLoc_s {
  // We don't define Loc type, since the only places it is used
  // are ghost
}

namespace LinearRegion_s {
  using namespace LinearRegion;
  using namespace LinearRegionRefCell_s;

  template <typename A>
  A Read(Region g, RefCell<A> r) {
    (void)g; // Avoid unused variable warning
    return *r;
  }

  template <typename A>
  A Borrow(Region g, RefCell<A> r) {
    return Read(g, r);
  }

  template <typename A>
  void Write(Region g, RefCell<A> r, A a) {
    (void)g; // Avoid unused variable warning
    *r = a;
  }

  template <typename A>
  void Swap(Region g, RefCell<A> r, A& a) {
    (void)g; // Avoid unused variable warning
    A tmp = a;
    a = *r;
    *r = tmp;
  }

  template <typename A>
  RefCell<A> Alloc(Region g, A a) {
    (void)g; // Avoid unused variable warning
    std::shared_ptr<A> ret = std::make_shared<A>();
    *ret = a;
    return ret;
  }

  template <typename A>
  RefCell<A> AllocLinear(Region g, A a) {
    return Alloc(g, a);
  }

  Region NewRegion() {
    Region ret;
    return ret;
  }

  void FreeRegion(Region g) {
    (void)g; // Avoid unused variable warning
  }

}

