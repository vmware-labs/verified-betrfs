include "../lib/Base/Option.s.dfy"
include "Allocation.i.dfy"

module CacheIfc {
  import opened Options
  import opened AllocationMod

  datatype Variables = Variables(dv:DiskView)

  predicate Init(s: Variables, mkfs:DiskView)
  {
    && FullView(mkfs)
    && s.dv == mkfs
  }

  function ReadValue(s: Variables, cu: CU) : Option<UninterpretedDiskPage>
  {
    if CanRead(s, cu) then Some(s.dv[cu]) else None
  }

  predicate Read(s: Variables, cu: CU, value: UninterpretedDiskPage)
  {
    && ReadValue(s, cu) == Some(value)
  }

  datatype Op = Write(cu: CU, value: UninterpretedDiskPage)
  type Ops == seq<Op>

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
