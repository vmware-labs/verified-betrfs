include "HTResource.i.dfy"

abstract module Main {
  import ARS = HTResource
  import Ifc = MapIfc
  import opened NativeTypes

  type Variables(==,!new) // using this name so the impl is more readable
  predicate Inv(v: Variables)

  method init(glinear in_r: ARS.R)
  returns (v: Variables, glinear out_r: ARS.R)
  requires ARS.Init(in_r)
  ensures Inv(v)

  method call(v: Variables, input: Ifc.Input,
      rid: int, glinear in_r: ARS.R, thread_id: uint32)
  returns (output: Ifc.Output, glinear out_r: ARS.R)
  decreases * // boi I don't feel bad about this
  requires Inv(v)
  requires in_r == ARS.input_ticket(rid, input)
  ensures out_r == ARS.output_stub(rid, output)
}

