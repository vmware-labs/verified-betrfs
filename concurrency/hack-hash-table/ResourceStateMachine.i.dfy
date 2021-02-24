include "HTResource.i.dfy"

module ResourceStateMachine {
  import opened KeyValueType

  import HT = HTResource
  import MapIfc

  type Variables = HT.R

  predicate Init(s: Variables)
  {
    HT.Init(s)
  }

  predicate Internal(s: Variables, s': Variables)
  {
    HT.Update(s, s')
  }

  predicate NewTicket(s: Variables, s': Variables, id: int, input: MapIfc.Input)
  {
    s' == HT.add(s, HT.input_ticket(input))
  }

  predicate ConsumeStub(s: Variables, s': Variables, id: int, output: MapIfc.Input)
  {
    s == HT.add(s', HT.output_stub(output))
  }

  ////// Invariant

  predicate Complete(s: Variables)
  {
    && (forall i | 0 <= i < |s.table| :: s.table[i].Some?)
  }

  predicate Inv(s: Variables)
  {
    && s.R?
    && Complete(s)
    && 
  }
}
