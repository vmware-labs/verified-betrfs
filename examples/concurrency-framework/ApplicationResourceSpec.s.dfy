include "ResourceSpec.s.dfy"

abstract module ApplicationResourceSpec(Ifc : InputOutputIfc) refines ResourceSpec {
  //function init_object() : R
  function input_ticket(id: int, input: Ifc.Input) : R
  function output_stub(id: int, output: Ifc.Output) : R
  // TODO some requirement that these are injective / don't overlap

  /*predicate Init(s) {
    s == {init_object()}
  }*/

  predicate NewTicket(s: multiset<R>, s': multiset<R>)
  {
    exists rid, input ::
      s' == s + multiset{input_ticket(rid, input)}
  }

  predicate ConsumeStub(s: multiset<R>, s': multiset<R>)
  {
    exists rid, output ::
      s == s' + multiset{output_ticket(rid, output)}
  }

  lemma NewTicketPreservesInv(s: multiset<R>, s': multiset<R>)
  requires Inv(s)
  requires NewTicket(s, s')
  ensures Inv(s')

  lemma ConsumeStubPreservesInv(s: multiset<R>, s': multiset<R>)
  requires Inv(s)
  requires ConstumeStub(s, s')
  ensures Inv(s')

  // refinement thm

  /*
  import AMS = AsyncSpec(MapIfc, MapSpec)

  function I(m: multiset<R>) : AMS.Variables

  lemma InitRefines(s: multiset<R>)
  requires Init(s)
  ensures AMS.Init(I(s))

  lemma NextRefines(s: multiset<R>, s': multiset<R>)
  requires Inv(s)
  requires Next(s, s')
  ensures AMS.Next(I(s), I(s'), AMS.Ifc.InternalOp)

  lemma NewTicketRefines(s: multiset<R>, s': multiset<R>)
  requires Inv(s)
  requires s' == s + {query_ticket(id, key)}
  ensures AMS.Next(I(s), I(s'), AMS.Ifc.Start(MapIfc.QueryRequest(key)))

  lemma EraseStubRefines(s: multiset<R>, s': multiset<R>)
  requires Inv(s)
  requires s == s' + {query_stub(id, value)}
  ensures AMS.Next(I(s), I(s'), AMS.Ifc.End(MapIfc.QueryResponse(value)))
  */
}
