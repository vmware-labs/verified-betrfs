// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

module ResourceSM(ARS : ApplicationResourceSpec) refines StateMachine(AsyncIfc(ARS.Ifc)) {
  datatype Variables = multiset<ARS.R>
  import Ifc = AsyncIfc(ARS.Ifc)

  predicate Next(s: Variables, s': Variables, op: Ifc.Op)
  {
    match op {
      case Start(rid, input) =>
        s' == s + multiset{ARS.input_ticket(rid, input)}
      case End(rid, output) =>
        s == s' + multiset{ARS.output_stub(rid, output)}
      case InternalOp =>
        ARS.Next(s, s')
    }
  }
}
