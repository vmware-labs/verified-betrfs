// This is the "burger" -- a middle layer of the sandwich that the .v adversary
// gets to define, but which meats obligations that impedance match between a
// thread-concurrent implementation below and an atomic state machine model
// above.

module ShardedIOMachine refines ResourceSpec {
  import SSM : ShardedStateMachine

  type Variables = SSM.Variables

  // Obligations
  function input_ticket(id: int, input: Ifc.Input) : R
  function output_stub(id: int, output: Ifc.Output) : R

  lemma NewTicketPreservesValid(r: R, id: int, input: Ifc.Input)
    requires Valid(r)
    ensures Valid(add(r, input_ticket(id, input)))

  // The resulting IO-enhanced state machine
  predicate Init(s: Variables)
  {
    SSM.Init(s)
  }

  predicate Internal(s: Variables, s': Variables)
  {
    SSM.Next(s, s')
  }

  predicate NewTicket(s: Variables, s': Variables, id: int, input: MapIfc.Input)
  {
    s' == SSM.add(s, SSM.input_ticket(id, input))
  }

  predicate ConsumeStub(s: Variables, s': Variables, id: int, output: MapIfc.Output)
  {
    s == SSM.add(s', SSM.output_stub(id, output))
  }
}
