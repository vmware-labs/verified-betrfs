// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/Option.s.dfy"
include "Allocation.i.dfy"

// Cache Interface that acts as the channel between the Betree/Journal/Program and the disk
module CacheIfc {
  import opened Options
  import opened DiskTypesMod
  import opened AllocationMod

  datatype Variables = Variables(dv:DiskView)

  predicate Mkfs(s: Variables, mkfs:DiskView)
  {
    && FullView(mkfs)
    && s.dv == mkfs
  }

  predicate Init(s: Variables)
  {
    && Empty(s.dv)
  }

  function ReadValue(s: Variables, cu: CU) : Option<UninterpretedDiskPage>
  {
    if cu in s.dv then Some(s.dv[cu]) else None
  }

  predicate Read(s: Variables, cu: CU, value: UninterpretedDiskPage)
  {
    && ReadValue(s, cu) == Some(value)
  }

  // Tells us if the value of this CU matches its value on disk
  predicate IsClean(s: Variables, cu: CU)
  {
    true // TODO
  }

  datatype Op = Write(cu: CU, value: UninterpretedDiskPage)
  type Ops = seq<Op>

  predicate WFOpSeq(ops: Ops) {
    forall i | 0<=i<|ops| :: ValidCU(ops[i].cu)
  }

  function IndexOfWrite(ops: Ops, cu: CU) : Option<nat>
  {
    if exists i :: 0<=i<|ops| && ops[i].cu == cu
    then var i :| 0<=i<|ops| && ops[i].cu == cu; Some(i)
    else None
  }

  function WriteAt(ops: Ops, cu: CU) : Option<UninterpretedDiskPage>
    requires WFOpSeq(ops)
  {
    var idx := IndexOfWrite(ops, cu);
    if idx.Some?
    then Some(ops[idx.value].value)
    else None
  }

  // TLA+-style partial actions
  predicate ApplyWrites(s: Variables, s': Variables, ops: Ops)
  {
    && FullView(s.dv)
    && FullView(s'.dv)
    && WFOpSeq(ops)
    && (forall cu | ValidCU(cu) ::
      s'.dv[cu] ==
        if WriteAt(ops, cu).Some?
        then WriteAt(ops, cu).value
        else s.dv[cu]
      )
  }
}
