// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

module LinearCollections {
  type LinearCollection<V>

  function multiset_of(lc: LinearCollection<V>) : multiset<V>

  function method empty()
    : (linear lc': LinearCollection<V>)
  ensures multiset_of(lc') == multiset{}

  method discard(linear lc: LinearCollection<V>)
  requires multiset_of(lc) == multiset{}

  function method add(linear lc: LinearCollection<V>, linear v: V)
    : (linear lc': LinearCollection<V>)
  ensures multiset_of(lc') == multiset_of(lc) + multiset{v}

  /*function method remove(linear lc: LinearCollection<V>, linear v: V)
    : (linear lc': LinearCollection<V>)
  requires v in multiset_of(lc)
  ensures multiset_of(lc') == multiset_of(lc) - multiset{v}*/
}
