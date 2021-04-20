include "HTResource.i.dfy"

abstract module Main {
  import ARS = HTResource
  import Ifc = MapIfc

  type Variables(==,!new) // using this name so the impl is more readable
  predicate Inv(v: Variables)

  method init(linear in_r: ARS.R)
  returns (v: Variables, linear out_r: ARS.R)
  requires ARS.Init(in_r)
  ensures Inv(v)

  method call(v: Variables, input: Ifc.Input,
      rid: int, linear in_r: ARS.R, thread_id: nat)
  returns (output: Ifc.Output, linear out_r: ARS.R)
  requires Inv(v)
  requires in_r == ARS.input_ticket(rid, input)
  ensures out_r == ARS.output_stub(rid, output)
}

