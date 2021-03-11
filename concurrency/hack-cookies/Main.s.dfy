// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "CookieResource.i.dfy"

abstract module Main {
  import ARS = CookieResource
  import Ifc = CookieIfc

  type Object(==,!new)
  predicate Inv(o: Object)

  method init(linear i: ARS.R)
  returns (o: Object)
  requires ARS.Init(i)
  ensures Inv(o)

  method call(o: Object, input: Ifc.Input,
      rid: int, linear ticket: ARS.R)
  returns (output: Ifc.Output, linear stub: ARS.R)
  requires Inv(o)
  requires ticket == ARS.input_ticket(rid, input)
  ensures stub == ARS.output_stub(rid, output)
}

