// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/Option.s.dfy"
include "../../lib/Lang/LinearSequence.i.dfy"
include "CompareAndSet.dfy"
include "Mutex.dfy"

module StateObjects {
  datatype Status = Unmatched | Reading | Clean | Dirty | Writing

  type Data

  datatype StateObject =
    | DiskBlockMatch(disk_idx: nat, cache_idx: nat)
    | DiskBlockUnmatched(disk_idx: nat)
    | CacheState(cache_idx: nat, data: Data, status: Status)

  method transform(linear cache_state: StateObject, linear unm: StateObject)
  returns (linear cache_state': StateObject, linear ma: StateObject)
  requires cache_state.CacheState?
  requires cache_state.status == Unmatched
  requires unm.DiskBlockUnmatched?

  ensures cache_state' == cache_state.(status := Reading)
  ensures ma == DiskBlockMatch(unm.disk_idx, cache_state.cache_idx)
}

module CacheMutex refines AbstractMutex {
  import opened StateObjects

  linear datatype CacheEntry = CacheEntry(
    linear data: Data,
    status: Status,
    linear r: StateObject)

  type ConstType = int
  type ValueType = CacheEntry

  predicate Inv(k: ConstType, v: ValueType)
  {
    && k >= 0
    && v.r == CacheState(k, v.data, v.status)
  }
}

module IndexCompareAndSwap refines AbstractCompareAndSet {
  import opened StateObjects

  type ConstType = int
  type ValueType = int
  type AbstractType = StateObject

  predicate Inv(k: ConstType, v: ValueType, a: AbstractType)
  {
    && (a.DiskBlockMatch? || a.DiskBlockUnmatched?)
    && (a.disk_idx == k)
    && (a.DiskBlockMatch? ==> a.cache_idx == v && v >= 0)
    && (a.DiskBlockUnmatched? ==> v == -1)
  }

  predicate compare_and_set_req(
      k: ConstType,
      old_v: ValueType,
      new_v: ValueType,
      ext_a: AbstractType)
  {
    && ext_a.CacheState?
    && ext_a.cache_idx == new_v
    && ext_a.status == Unmatched
    && old_v == -1
  }

  predicate compare_and_set_guarantee(
      k: ConstType,
      old_v: ValueType,
      new_v: ValueType,
      set_success: bool,
      ext_a: AbstractType,
      ext_a': AbstractType)
  {
    && (!set_success ==> ext_a' == ext_a)
    && (set_success ==>
      && ext_a.CacheState?
      && ext_a' == CacheState(ext_a.cache_idx, ext_a.data, Reading)
    )
  }

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
  {
    if set_success {
      ext_a', int_a' := transform(ext_a, int_a);
    } else {
      ext_a' := ext_a;
      int_a' := int_a;
    }
  }
}

module Impl {
  import opened StateObjects
  import opened IndexCompareAndSwap
  import opened CacheMutex

  datatype Cache = Cache(
    disk_idx_to_cache_idx: seq<Cell>,
    cache_data: seq<Mutex>
  )

  const cache: Cache;

  predicate Inv(cache: Cache)
  {
    && (forall i | 0 <= i < |cache.disk_idx_to_cache_idx|
        :: cache.disk_idx_to_cache_idx[i].constant() == i)
    && (forall i | 0 <= i < |cache.cache_data|
        :: cache.cache_data[i].constant() == i)
  }

  method page_in(disk_idx: int, cache_idx: int)
  requires Inv(cache)
  requires 0 <= disk_idx < |cache.disk_idx_to_cache_idx| < 0x1_0000_0000_0000_0000
  requires 0 <= cache_idx < |cache.cache_data| < 0x1_0000_0000_0000_0000
  {
    linear var cache_entry := acquire(cache.cache_data[cache_idx]);
    assert cache.cache_data[cache_idx].constant() == cache_idx;
    assert CacheMutex.Inv(cache_idx, cache_entry);

    if cache_entry.status != Unmatched {
      // bail out
      release(cache.cache_data[cache_idx], cache_entry);
    } else {
      var compare_and_set_succ;
      linear var r';

      linear var CacheEntry(data, status, r) := cache_entry;

      assert compare_and_set_req(
          cache.disk_idx_to_cache_idx[disk_idx].constant(),
          -1, cache_idx, r);
      compare_and_set_succ, r' := compare_and_set(
            cache.disk_idx_to_cache_idx[disk_idx],
            -1, cache_idx,
            r);

      linear var cache_entry';

      if compare_and_set_succ {
        cache_entry' := CacheEntry(data, Reading, r');
      } else {
        cache_entry' := CacheEntry(data, status, r');
      }

      assert CacheMutex.Inv(cache_idx, cache_entry');
      release(cache.cache_data[cache_idx], cache_entry');
    }
  }
}
