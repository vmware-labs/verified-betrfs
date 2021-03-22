// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

abstract module Main(ARS: ApplicationResourceSpec) {
  type Object(==,!new)
  predicate Inv(o: Object)

  method init(ghost linear i: ARS.R)
  returns (o: Object)
  requires i == ARS.init_object()
  ensures Inv(o)

  method call(o: Object, input: Input,
      ghost rid: int, ghost linear ticket: ARS.R)
  returns (output: Output, ghost linear stub: ARS.R)
  requires Inv(o)
  requires ticket == ARS.input_ticket(rid, key)
  ensures stub == ARS.output_stub(rid, stub)
}

