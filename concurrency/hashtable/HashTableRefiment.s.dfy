include "HashTableStubSSM.s.dfy"

module HashTableRefiment refines
  Refinement(AsyncIfc(MapIfc),
    TicketStubStateMachine(MapIfc, HashTableStubSSM),
    AsyncStateMachine(MapIfc, MapSpec))
{
  import SSM = HashTableStubSSM
  import SM = StateMachine(MapIfc)
  import CircularTable
  import MapSpec

  // import A = TicketStubStateMachine(MapIfc, HashTableStubSSM)
  // import B = AsyncStateMachine(MapIfc, MapSpec)

  // repeated?
  predicate Inv(s: A.Variables)
  {
    SSM.Inv(s)
  }

  // repeated?
  lemma InitImpliesInv(s: A.Variables)
  {
    SSM.InitImpliesInv(s);
  }

  lemma NextPreservesInv(s: A.Variables, s': A.Variables, op: ifc.Op)
  {
    match op
      case Start(rid, input) =>
        SSM.NewTicketPreservesInv(s, s', rid, input);
      case End(rid, output) =>
        SSM.ConsumeStubPreservesInv(s, s', rid, output);
      case InternalOp => {
        assert exists shard, shard', rest :: A.InternalNext(s, s', shard, shard', rest);
        var shard, shard', rest :| A.InternalNext(s, s', shard, shard', rest);
        SSM.InternalPreservesInv(shard, shard', rest);
      }
  }

  function I(s: A.Variables) : B.Variables
  {
    var m := CircularTable.I(s.table);
    B.Variables(
      MapSpec.Variables(m),
      s.reqs, s.resps)
  }
}
