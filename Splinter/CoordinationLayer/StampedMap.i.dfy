// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Base/KeyType.s.dfy"
include "../../Spec/Message.s.dfy"
include "../../Spec/TotalKMMap.s.dfy"
include "LSNMod.i.dfy"

// A "StampedMap" is a full imap "stamped" with an LSN that identifies how many
// operations it represents.
module StampedMod {
  import opened ValueMessage
  import opened KeyType
  import opened TotalKMMapMod
  import opened LSNMod

  datatype Stamped<T> = Stamped(value: T, seqEnd: LSN)

  type StampedMap = Stamped<TotalKMMap>

  function Empty() : StampedMap
  {
    StampedMap(EmptyTotalMap(), 0)
  }
}
