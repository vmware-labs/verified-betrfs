include "HashTableStubSSM.s.dfy"

module HashTableRefiment refines
  Refinement(AsyncIfc(MapIfc),
    TicketStubStateMachine(MapIfc, HashTableStubSSM),
    AsyncStateMachine(MapIfc, MapSpec))
{
  import opened KeyValueType
  import MapSpec
  import MapIfc

  import SSM = HashTableStubSSM
  import SM = StateMachine(MapIfc)
  import opened CircularTable
  import opened CircularRange

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
    B.Variables(MapSpec.Variables(m), s.reqs, s.resps)
  }

  lemma InitRefinesInit(s: A.Variables)
  {
    CircularTable.EmptyTableEmptyMap(s.table);
  }

  lemma InsertRefinesMap(s: A.Variables, s': A.Variables, step: SSM.Step) 
    returns (output: MapIfc.Output)
    requires Inv(s) && Inv(s')
    requires step.InsertStep? && SSM.NextStep(s, s', step)
    requires step.input.InsertInput?
    ensures MapSpec.Next(
      MapSpec.Variables(I(s).s.m),
      MapSpec.Variables(I(s').s.m),
      MapIfc.Op(step.input, output))
    ensures s'.reqs == s.reqs - {step.rid}
    ensures s'.resps == s.resps[step.rid := output]
  {
    var InsertStep(rid, input, start, end) := step;
    assert input.InsertInput?;
    var InsertInput(key, value) := input;
    var table, table' := s.table, s'.table;
    var inserted := Full(key, value);

    var p_range := Partial(hash(key), start);
    ProbeRangeSufficient(table, key, p_range);
    ContainmentEquivalent(table, key);
    RightShiftPreservesMapping(table, table', inserted);

    var si, si' := I(s), I(s');
    var m, m' := si.s.m, si'.s.m;

    assert m' == m[key := value];
    output := MapIfc.InsertOutput(true);
  }

  lemma OverwriteRefinesMap(s: A.Variables, s': A.Variables, step: SSM.Step)
    returns (output: MapIfc.Output)
    requires Inv(s) && Inv(s')
    requires step.OverwriteStep? && SSM.NextStep(s, s', step)
    requires step.input.InsertInput?
    ensures MapSpec.Next(
      MapSpec.Variables(I(s).s.m),
      MapSpec.Variables(I(s').s.m),
      MapIfc.Op(step.input, output))
    ensures s'.reqs == s.reqs - {step.rid}
    ensures s'.resps == s.resps[step.rid := output]
  {
    var OverwriteStep(rid, input, end) := step;
    assert input.InsertInput?;
    var InsertInput(key, value) := input;
    var table, table' := s.table, s'.table;
    var inserted := Full(key, value);

    ContainmentEquivalent(table, key);
    OverwritePreservesMapping(table, table', end, inserted);

    var si, si' := I(s), I(s');
    var m, m' := si.s.m, si'.s.m;

    assert m' == m[key := value];

    output := MapIfc.InsertOutput(true);
  }

  lemma RemoveRefinesMap(s: A.Variables, s': A.Variables, step: SSM.Step)
    returns (output: MapIfc.Output)
    requires Inv(s) && Inv(s')
    requires step.RemoveStep? && SSM.NextStep(s, s', step)
    requires step.input.RemoveInput?
    ensures MapSpec.Next(
      MapSpec.Variables(I(s).s.m),
      MapSpec.Variables(I(s').s.m),
      MapIfc.Op(step.input, output))
    ensures s'.reqs == s.reqs - {step.rid}
    ensures s'.resps == s.resps[step.rid := output]
  {
    var RemoveStep(rid, input, start, end) := step;
    var key := input.key;
    var table, table' := s.table, s'.table;

    ContainmentEquivalent(table, key);
    LeftShiftPreservesMapping(table, table', key);

    var si, si' := I(s), I(s');
    var m, m' := si.s.m, si'.s.m;

    assert m' == m - {key};
    output := MapIfc.RemoveOutput(true);
  }

  lemma RemoveNotFoundRefinesMap(s: A.Variables, s': A.Variables, step: SSM.Step)
    returns (output: MapIfc.Output)
    requires Inv(s) && Inv(s')
    requires step.RemoveNotFoundStep? && SSM.NextStep(s, s', step)
    requires step.input.RemoveInput?
    ensures MapSpec.Next(
      MapSpec.Variables(I(s).s.m),
      MapSpec.Variables(I(s').s.m),
      MapIfc.Op(step.input, output))
    ensures s'.reqs == s.reqs - {step.rid}
    ensures s'.resps == s.resps[step.rid := output]
  {
    var RemoveNotFoundStep(rid, input, end) := step;
    var key := input.key;
    var table, table' := s.table, s'.table;
    var p_range := Partial(hash(key), end);
    ProbeRangeSufficient(table, key, p_range);

    ContainmentEquivalent(table, key);

    var si, si' := I(s), I(s');
    var m, m' := si.s.m, si'.s.m;
    assert key !in m;

    output := MapIfc.RemoveOutput(false);
  }

  lemma QueryNotFoundRefinesMap(s: A.Variables, s': A.Variables, step: SSM.Step)
    returns (output: MapIfc.Output)
    requires Inv(s) && Inv(s')
    requires step.QueryNotFoundStep? && SSM.NextStep(s, s', step)
    requires step.input.QueryInput?
    ensures MapSpec.Next(
      MapSpec.Variables(I(s).s.m),
      MapSpec.Variables(I(s').s.m),
      MapIfc.Op(step.input, output))
    ensures s'.reqs == s.reqs - {step.rid}
    ensures s'.resps == s.resps[step.rid := output]
  {
    var QueryNotFoundStep(rid, input, end) := step;
    var key := input.key;
    var table, table' := s.table, s'.table;
    var p_range := Partial(hash(key), end);
    ProbeRangeSufficient(table, key, p_range);

    ContainmentEquivalent(table, key);

    var si, si' := I(s), I(s');
    var m, m' := si.s.m, si'.s.m;
    assert key !in m;

    output := MapIfc.QueryOutput(QueryResult.NotFound);
  }

  lemma QueryFoundRefinesMap(s: A.Variables, s': A.Variables, step: SSM.Step)
    returns (output: MapIfc.Output)
    requires Inv(s) && Inv(s')
    requires step.QueryFoundStep? && SSM.NextStep(s, s', step)
    requires step.input.QueryInput?
    ensures MapSpec.Next(
      MapSpec.Variables(I(s).s.m),
      MapSpec.Variables(I(s').s.m),
      MapIfc.Op(step.input, output))
    ensures s'.resps == s.resps[step.rid := output]
  {
    var QueryFoundStep(rid, input, end) := step;
    var key := input.key;
    var table := s.table;

    ContainmentEquivalent(table, key);

    var si, si' := I(s), I(s');
    var m := si.s.m;

    assert key in m && m[key] == table[end].value.value;
    output := MapIfc.QueryOutput(QueryResult.Found(m[key]));
  }

  lemma InternalRefinesMap(s: A.Variables, s': A.Variables)
    requires Inv(s)
    requires SSM.Internal(s, s')
    ensures Inv(s')
    ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    var step: SSM.Step :| SSM.NextStep(s, s', step); 
    SSM.NextStepPreservesInv(s, s');

    var si, si' := I(s), I(s');

    var rid, input := step.rid, step.input;

    var output;

    if step.InsertStep? {
      output := InsertRefinesMap(s, s', step);
    } else if step.OverwriteStep? {
      output := OverwriteRefinesMap(s, s', step);
    } else if step.QueryFoundStep? {
      output := QueryFoundRefinesMap(s, s', step);
    } else if step.QueryNotFoundStep? {
      output := QueryNotFoundRefinesMap(s, s', step);
    } else if step.RemoveStep? {
      output := RemoveRefinesMap(s, s', step);
    } else if step.RemoveNotFoundStep? {
      output := RemoveNotFoundRefinesMap(s, s', step);
    } else {
      assert false;
    }

    assert B.Next(si, si', ifc.InternalOp) by {
      assert B.InteralNext(rid, input, output, si, si');
    }
  }

  lemma NextRefinesNext(s: A.Variables, s': A.Variables, op: ifc.Op)
  {
    match op
      case Start(rid, input) =>
        assert s' == s.(reqs := s.reqs[rid := input]);
        assert I(s') == I(s).(reqs := I(s).reqs[rid := input]);
      case End(rid, output) =>
        assert s == s'.(resps := s'.resps[rid := output]);
        assert I(s) == I(s').(resps := I(s').resps[rid := output]);
      case InternalOp => {
        assert exists shard, shard', rest :: A.InternalNext(s, s', shard, shard', rest);
        var shard, shard', rest :| A.InternalNext(s, s', shard, shard', rest);
        SSM.InternalPreservesInv(shard, shard', rest);
        SSM.InternalMonotonic(shard, shard', rest);
        InternalRefinesMap(s, s');
      }
  }
}
