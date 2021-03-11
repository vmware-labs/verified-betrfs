// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

abstract module AbstractCompareAndSet {
  type ConstType
  type ValueType
  type AbstractType

  predicate Inv(k: ConstType, v: ValueType, a: AbstractType)

  type OpaqueType
  datatype Cell = Cell(x: OpaqueType)
  {
    function {:axiom} constant() : ConstType
  }

  // Constructor

  method {:axiom} new_cell(k: ConstType, v: ValueType, a: AbstractType)
  returns (cell: Cell)
  requires Inv(k, v, a)
  ensures cell.constant() == k

  // compare_and_set

  predicate compare_and_set_req(
      k: ConstType,
      old_v: ValueType,
      new_v: ValueType,
      ext_a: AbstractType)

  predicate compare_and_set_guarantee(
      k: ConstType,
      old_v: ValueType,
      new_v: ValueType,
      set_success: bool,
      ext_a: AbstractType,
      ext_a': AbstractType)

  method {:axiom} compare_and_set(
      cell: Cell,
      old_v: ValueType,
      new_v: ValueType,
      linear ext_a: AbstractType)
  returns (set_success: bool, linear ext_a': AbstractType)
  requires compare_and_set_req(cell.constant(), old_v, new_v, ext_a)
  ensures compare_and_set_guarantee(cell.constant(), old_v, new_v, set_success, ext_a, ext_a')

  method compare_and_set_internal_change(
      k: ConstType,
      int_v: ValueType,
      int_v': ValueType,

      old_v: ValueType,
      new_v: ValueType,
      set_success: bool,

      linear int_a: AbstractType,
      linear ext_a: AbstractType)
  returns (linear int_a': AbstractType, linear ext_a': AbstractType)
  requires Inv(k, int_v, int_a)
  requires set_success ==> int_v == old_v && int_v' == new_v
  requires !set_success ==> int_v != old_v && int_v' == int_v
  requires compare_and_set_req(k, old_v, new_v, ext_a)

  ensures Inv(k, int_v', int_a')
  ensures compare_and_set_guarantee(k, old_v, new_v, set_success, ext_a, ext_a')
}
