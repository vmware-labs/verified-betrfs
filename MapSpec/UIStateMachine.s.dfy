// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "../MapSpec/UI.s.dfy"

// Abstract module for state machines with transitions labeled by UIOps.
// Provides a little bit of convenience for abstracting things over
// state machines.

abstract module UIStateMachine {
  import myUI = UI
  type UIOp = myUI.Op

  type Variables(!new)
  predicate Init(s: Variables)
  predicate Next(s: Variables, s': Variables, uiop: UIOp)

  predicate Inv(s: Variables)

  lemma InitImpliesInv(s: Variables)
  requires Init(s)
  ensures Inv(s)

  lemma NextPreservesInv(s: Variables, s': Variables, uiop: UIOp)
  requires Inv(s)
  requires Next(s, s', uiop)
  ensures Inv(s')
}
