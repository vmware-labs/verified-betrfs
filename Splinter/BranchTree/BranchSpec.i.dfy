// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/Option.s.dfy"
include "../../lib/Base/KeyType.s.dfy"
include "../../Spec/Message.s.dfy"

module BranchSpec {
  import opened Options
  import opened ValueMessage
  import opened KeyType

  type Map = map<Key, Message>
  datatype Variables = Variables(mapp: Map)

  predicate Init(v:Variables)
  {
    && v.mapp == map[]
  }

  predicate Insert(v:Variables, v': Variables, k: Key, m: Message)
  {
    && v'.mapp == v.mapp[k := m]
  }

  predicate Discard(v:Variables, v': Variables, discardKeys: set<Key>)
  {
    && v'.mapp == map k | k in v.mapp && k !in discardKeys :: v.mapp[k]
  }

  predicate Query(v:Variables, v': Variables, k: Key, m: Option<Message>)
  {
    && (m.Some? <==> k in v.mapp)         // report whether k is present
    && (m.Some? ==> v.mapp[k] == m.value) // report the correct value
  }
}
