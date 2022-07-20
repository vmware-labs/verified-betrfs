// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "GenericDisk.i.dfy"

module AUAddress refines AddressTypeMod {
  type AU = nat
  type Page = nat

  function PageSize() : nat

  datatype Address = Address(au: AU, page: Page)
}
