// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "TotalMap.s.dfy"

module TotalKMMapMod refines TotalMapMod {
  import opened ValueMessage
  import opened KeyType
  // Defines a fully-populated Key-Message imap

  type K = Key
  type V = Message
  predicate TerminalValue(v: V) { v.Define? }
  function DefaultV() : V { DefaultMessage() }

  type TotalKMMap = TotalMap
}
