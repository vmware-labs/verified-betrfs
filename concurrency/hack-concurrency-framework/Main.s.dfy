// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

abstract module Main(ARS: ApplicationResourceSpec) {
  type Object(==,!new)
  predicate Inv(o: Object)

  method init(ghost linear i: ARS.R)
  returns (o: Object)
  requires i == ARS.init_object()
  ensures Inv(o)

  method query(o: Object, key: int,
      ghost rid: int, ghost linear ticket: ARS.R)
  returns (value: int, ghost linear stub: ARS.R)
  requires Inv(o)
  requires ticket == ARS.query_ticket(rid, key)
  ensures stub == ARS.query_stub(rid, stub)
}

abstract module AllTogether(
    SM: ResourceStateMachine,
    M: Main(SM.ARS),
    refinement: StateMachineRefinement(SM, AsyncSpec(MapSpec))
)
