// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Spec/MapSpec.s.dfy"
include "../lib/Base/MapRemove.s.dfy"
include "../lib/Checksums/CRC32C.s.dfy"
include "AsyncDisk.s.dfy"
include "AsyncDiskProgram.s.dfy"
include "IOSystem.s.dfy"


abstract module ProofObligations {
  import CrashTolerantMapSpecMod
  import ConcreteSystem : IOSystem

  // Your interpretation function
  function I(v: ConcreteSystem.Variables) : CrashTolerantMapSpecMod.Variables

  // Your system invariant
  predicate Inv(v: ConcreteSystem.Variables)

  lemma InitRefines(v: ConcreteSystem.Variables)
    requires ConcreteSystem.Init(v)
    ensures CrashTolerantMapSpecMod.Init(I(v))
    ensures Inv(v)

  lemma NextRefines(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp)
    requires Inv(v)
    requires ConcreteSystem.Next(v, v', uiop)
    ensures Inv(v')
    ensures CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop)

}
