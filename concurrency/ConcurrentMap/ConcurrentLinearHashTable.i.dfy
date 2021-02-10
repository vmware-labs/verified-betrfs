include "../../lib/Base/sequences.i.dfy"
include "ConcurrentMap.i.dfy"

abstract module LocalModel {
  type SharedVariables
}

module LocalConcurrentLinearHashTable refines LocalModel {
  import ConcurrentMap

  type Key = ConcurrentMap.Key
  type Value = ConcurrentMap.Value

  datatype Item = Empty | Entry(key: Key, value: Value) | Tombstone(key: Key)

  // Implementation uses sequence of Items:
  datatype SharedVariables = SharedVariables(table: seq<Item>)

  datatype Slot = Slot(slot: nat)

  datatype ThreadState =
    | Insert(key: Key, value: Value, slot:Slot)
    //| Remove(key: Key, slot:Slot)
    | Query(key: Key, slot:Slot)
    | Idle

  predicate WFThreadState(elementsLength: nat, t: ThreadState)
  {
    match t
      case Insert(_, _, slot) => ValidSlot(elementsLength, slot)
      //case Remove(_, slot) => ValidSlot(elementsLength, slot)
      case Query(_, slot) => ValidSlot(elementsLength, slot)
      case Idle => true
  }

  predicate ValidSlot(elementsLength: nat, slot: Slot)
  {
    slot.slot < elementsLength
  }

   function method SlotForKey(elementsLength: nat, key: Key): (result: Slot)
   requires 0 < elementsLength
   ensures ValidSlot(elementsLength, result)
   //  {
   //    var h := hash64(key);
   //    Slot((h as nat) % elementsLength)
   //  }

  predicate InsertInit(s:SharedVariables, s':SharedVariables, t: ThreadState, t': ThreadState, key:Key, value:Value)
  {
    && WFThreadState(|s.table|, t)
    && |s.table| > 0
    && t.Idle?
    && t' == Insert(key, value, SlotForKey(|s.table|, key))
    && s' == s
  }

  predicate InsertAdvance(s:SharedVariables, s':SharedVariables, t:ThreadState, t':ThreadState)
  {
    && WFThreadState(|s.table|, t)
    && t.Insert?
    && !s.table[t.slot.slot].Empty?
    && s.table[t.slot.slot].key != t.key
    && t.slot.slot < |s.table|-1  // Can't roll around end of table
    && s' == s
    && t' == t.(slot := Slot(t.slot.slot+1))
  }

  predicate InsertComplete(s:SharedVariables, s':SharedVariables, t: ThreadState, t': ThreadState)
  {
    && WFThreadState(|s.table|, t)
    && t.Insert?
    && t'.Idle?
    && (s.table[t.slot.slot].Empty? || s.table[t.slot.slot].key == t.key)
    && s' == s.(table := s.table[t.slot.slot := Entry(t.key, t.value)])
  }

  predicate QueryInit(s:SharedVariables, s':SharedVariables, t: ThreadState, t': ThreadState, key:Key)
  {
    && 0 < |s.table|
    && WFThreadState(|s.table|, t)
    && t.Idle?
    && s' == s
    && t' == Query(key, SlotForKey(|s.table|, key))
  }

  predicate QueryAdvance(s:SharedVariables, s':SharedVariables, t: ThreadState, t': ThreadState)
  {
    && WFThreadState(|s.table|, t)
    && t.Query?
    && !s.table[t.slot.slot].Empty?
    && s.table[t.slot.slot].key != t.key
    && t.slot.slot < |s.table|-1  // Can't roll around end of table TODO
    && t' == t.(slot := Slot(t.slot.slot+1))
    && s' == s
  }

  // TODO Success-only result; need to return None
  predicate QueryComplete(s:SharedVariables, s':SharedVariables, t: ThreadState, t': ThreadState, value:Value)
  {
    && WFThreadState(|s.table|, t)
    && t.Query?
    && t'.Idle?
    && s.table[t.slot.slot] == Entry(t.key, value)
    && s' == s
  }

  datatype Step =
    | InsertInitStep(key:Key, value:Value)
    | InsertAdvanceStep
    | InsertCompleteStep
    | QueryInitStep(key:Key)
    | QueryAdvanceStep
    | QueryCompleteStep(value:Value)

  predicate NextStep(s:SharedVariables, s':SharedVariables, t: ThreadState, t': ThreadState, step:Step) {
    match step {
      case InsertInitStep(key, value) => InsertInit(s, s', t, t', key, value)
      case InsertAdvanceStep => InsertAdvance(s, s', t, t')
      case InsertCompleteStep => InsertComplete(s, s', t, t')
      case QueryInitStep(key) => QueryInit(s, s', t, t', key)
      case QueryAdvanceStep => QueryAdvance(s, s', t, t')
      case QueryCompleteStep(value) => QueryComplete(s, s', t, t', value)
    }
  }

  predicate Next(s:SharedVariables, s':SharedVariables, t: ThreadState, t': ThreadState) {
    exists step:Step :: NextStep(s, s', t, t', step)
  }
}

module ConcurrentLinearHashTable {
  import opened L = LocalConcurrentLinearHashTable
  import ConcurrentMap

  import opened Sequences
  import opened Options


  datatype Variables = Variables(
      sv: L.SharedVariables,
      threads: map<nat, L.ThreadState>
  )

  predicate ValidThreadId(s:Variables, tid:nat)
  {
    tid in s.threads
  }

  predicate WFVariables(s:Variables)
  {
    && 0 < |s.sv.table|
    && (forall tid | ValidThreadId(s, tid) :: WFThreadState(|s.sv.table|, s.threads[tid]))
  }

  predicate Init(s:Variables) {
    && |s.sv.table| > 0
    && (forall si | 0<=si<|s.sv.table| :: s.sv.table[si].Empty?)
    && (forall tid | tid in s.threads :: s.threads[tid].Idle?)
  }

  predicate NextThread(s:Variables, s':Variables, tid: nat) {
    && tid in s.threads
    && tid in s'.threads
    && L.Next(s.sv, s'.sv, s.threads[tid], s'.threads[tid])
    && s'.threads == s.threads[tid := s'.threads[tid]]
  }

  predicate Next(s:Variables, s':Variables) {
    exists tid:nat :: NextThread(s, s', tid)
  }

  function ITable(table:seq<L.Item>) : (m:map<Key,Value>)
    ensures forall slot | ValidSlot(|table|, slot) && table[slot.slot].Entry?  :: table[slot.slot].key in m
  {
    if |table|==0
      then map[]
    else
      var last := Last(table);
      if last.Entry?
        then ITable(DropLast(table))[last.key := last.value]
        else ITable(DropLast(table))
  }

  predicate KeySlot(table:seq<L.Item>, slot:L.Slot)
  {
    && ValidSlot(|table|, slot)
    && !table[slot.slot].Empty?
  }

  predicate UniqueKeys(table:seq<L.Item>)
  {
    (forall i, j | && KeySlot(table, i) && KeySlot(table, j) && table[i.slot].key == table[j.slot].key
      :: i == j)
  }

  predicate ReachableForKey(table:seq<L.Item>, key:Key, end /* exclusive */ :L.Slot)
  {
    && 0<|table|
    && ValidSlot(|table|, end)
    && var start := SlotForKey(|table|, key);
    && start.slot <= end.slot
    && (forall i:L.Slot | start.slot<=i.slot<end.slot :: !table[i.slot].Empty? && table[i.slot].key!=key)
  }

  predicate ReachableInv(table:seq<L.Item>)
  {
    (forall i | KeySlot(table, i) :: ReachableForKey(table, table[i.slot].key, i))
  }

  predicate TableInv(table:seq<L.Item>)
  {
    && UniqueKeys(table)
    && ReachableInv(table)
  }

  predicate ThreadInv(s:Variables, t:L.ThreadState)
  {
    !t.Idle? ==> ReachableForKey(s.sv.table, t.key, t.slot)
  }

  predicate Inv(s:Variables)
  {
    && TableInv(s.sv.table)
    && (forall tid | ValidThreadId(s, tid) :: ThreadInv(s, s.threads[tid]))
  }

  lemma InitImpliesInv(s:Variables)
  requires Init(s)
  ensures Inv(s)
  {
  }

  lemma NextPreservesInv(s:Variables, s':Variables)
  requires Next(s, s')
  requires Inv(s)
  ensures Inv(s')
  {
  }

  lemma InsertInitInterpretation(s:Variables, s':Variables, tid:nat, key:Key, value:Value)
    requires Inv(s)
    requires ValidThreadId(s, tid)
    requires ValidThreadId(s', tid)
    requires s'.threads == s.threads[tid := s'.threads[tid]]
    requires InsertInit(s.sv, s'.sv, s.threads[tid], s'.threads[tid], key, value)
    ensures Inv(s')
    ensures ITable(s'.sv.table) == ITable(s.sv.table)
  {
  }

  lemma InsertAdvanceInterpretation(s:Variables, s':Variables, tid:nat)
    requires Inv(s)
    requires ValidThreadId(s, tid)
    requires ValidThreadId(s', tid)
    requires s'.threads == s.threads[tid := s'.threads[tid]]
    requires InsertAdvance(s.sv, s'.sv, s.threads[tid], s'.threads[tid])
    ensures Inv(s')
    ensures ITable(s'.sv.table) == ITable(s.sv.table)
  {
  }

  lemma PointInterpretationForwards(table: seq<L.Item>, i: L.Slot)
    requires UniqueKeys(table)
    requires KeySlot(table, i)
    requires table[i.slot].Entry?
    ensures table[i.slot].key in ITable(table) && ITable(table)[table[i.slot].key] == table[i.slot].value
  {
    if |table| == i.slot + 1 {
    } else {
      PointInterpretationForwards(DropLast(table), i);
      if Last(table).Entry? {
        assert KeySlot(table, L.Slot(|table|-1));
      }
    }
  }

  lemma PointInterpretationBackwards(table: seq<L.Item>)
    requires UniqueKeys(table)
    ensures forall k | k in ITable(table) :: exists i :: KeySlot(table, i) && table[i.slot] == Entry(k, ITable(table)[k])
  {
    if |table| == 0 {
    } else {
      PointInterpretationBackwards(DropLast(table));
      var prem := ITable(DropLast(table));
      var m := ITable(table);
      forall k | k in ITable(table)
      ensures exists i :: KeySlot(table, i) && table[i.slot] == Entry(k, ITable(table)[k])
      {
        var l := Last(table);
        if (l.Entry? || l.Tombstone?) && k == l.key {
          var i := L.Slot(|table| - 1);
          assert KeySlot(table, i);
          assert table[i.slot] == Entry(k, ITable(table)[k]);
        } else {
          assert exists i :: KeySlot(table, i) && table[i.slot] == Entry(k, ITable(table)[k]);
        }
      }
    }
  }

  lemma PointInterpretation(table: seq<L.Item>)
    requires UniqueKeys(table)
    ensures forall i | KeySlot(table, i) && table[i.slot].Entry? :: table[i.slot].key in ITable(table) && ITable(table)[table[i.slot].key] == table[i.slot].value
    ensures forall k | k in ITable(table) :: exists i :: KeySlot(table, i) && table[i.slot] == Entry(k, ITable(table)[k])
  {
    forall i | KeySlot(table, i) && table[i.slot].Entry?
      ensures table[i.slot].key in ITable(table) && ITable(table)[table[i.slot].key] == table[i.slot].value
    {
      PointInterpretationForwards(table, i);
    }
    PointInterpretationBackwards(table);
  }

  lemma InsertCompleteInterpretation(s:Variables, s':Variables, tid:nat)
    requires Inv(s)
    requires ValidThreadId(s, tid)
    requires ValidThreadId(s', tid)
    requires s'.threads == s.threads[tid := s'.threads[tid]]
    requires InsertComplete(s.sv, s'.sv, s.threads[tid], s'.threads[tid])
    ensures Inv(s')
    ensures ITable(s'.sv.table) == ITable(s.sv.table)[s.threads[tid].key := s.threads[tid].value]
  {
    PointInterpretation(s.sv.table);
    PointInterpretation(s'.sv.table);
  }

  lemma QueryInitInterpretation(s:Variables, s':Variables, tid:nat, key: Key)
    requires Inv(s)
    requires ValidThreadId(s, tid)
    requires ValidThreadId(s', tid)
    requires s'.threads == s.threads[tid := s'.threads[tid]]
    requires QueryInit(s.sv, s'.sv, s.threads[tid], s'.threads[tid], key)
    ensures Inv(s')
    ensures ITable(s'.sv.table) == ITable(s.sv.table)
  {
  }

  lemma QueryAdvanceInterpretation(s:Variables, s':Variables, tid:nat)
    requires Inv(s)
    requires ValidThreadId(s, tid)
    requires ValidThreadId(s', tid)
    requires s'.threads == s.threads[tid := s'.threads[tid]]
    requires QueryAdvance(s.sv, s'.sv, s.threads[tid], s'.threads[tid])
    ensures Inv(s')
    ensures ITable(s'.sv.table) == ITable(s.sv.table)
  {
  }

  lemma QueryCompleteInterpretation(s:Variables, s':Variables, tid:nat, value: Value)
    requires Inv(s)
    requires ValidThreadId(s, tid)
    requires ValidThreadId(s', tid)
    requires s'.threads == s.threads[tid := s'.threads[tid]]
    requires QueryComplete(s.sv, s'.sv, s.threads[tid], s'.threads[tid], value)
    ensures Inv(s')
    ensures ITable(s'.sv.table) == ITable(s.sv.table)
  {
  }

  function IThread(t: L.ThreadState) : ConcurrentMap.Req
  requires t != Idle
  {
    match t {
      case Insert(key, value, slot) => ConcurrentMap.ReqInsert(key, value)
      case Query(key, slot) => ConcurrentMap.ReqQuery(key)
    }
  }

  function I(s: Variables): ConcurrentMap.Variables
  {
    ConcurrentMap.Variables(
      ITable(s.sv.table),
      map tid:nat | tid in s.threads && s.threads[tid] != Idle
          :: IThread(s.threads[tid])
    ) 
  }

  lemma InsertInitStepRefinesNext(s: Variables, s': Variables, key: Key, value: Value, tid: nat)
    requires Inv(s)
    requires ValidThreadId(s, tid)
    requires ValidThreadId(s', tid)
    requires s'.threads == s.threads[tid := s'.threads[tid]]
    requires InsertInit(s.sv, s'.sv, s.threads[tid], s'.threads[tid], key, value)
    ensures Inv(s')
    ensures ConcurrentMap.Next(I(s), I(s'))
  {
    assert ConcurrentMap.NextStep(I(s), I(s'),
        ConcurrentMap.InsertStartStep(tid, key, value));
  }

  lemma InsertAdvanceStepRefinesNext(s: Variables, s': Variables, tid: nat)
    requires Inv(s)
    requires ValidThreadId(s, tid)
    requires ValidThreadId(s', tid)
    requires s'.threads == s.threads[tid := s'.threads[tid]]
    requires InsertAdvance(s.sv, s'.sv, s.threads[tid], s'.threads[tid])
    ensures Inv(s')
    ensures ConcurrentMap.Next(I(s), I(s'))
  {
    assert ConcurrentMap.NextStep(I(s), I(s'), ConcurrentMap.NoOpStep);
  }

  lemma InsertCompleteStepRefinesNext(s: Variables, s': Variables, tid: nat)
    requires Inv(s)
    requires ValidThreadId(s, tid)
    requires ValidThreadId(s', tid)
    requires s'.threads == s.threads[tid := s'.threads[tid]]
    requires InsertComplete(s.sv, s'.sv, s.threads[tid], s'.threads[tid])
    ensures Inv(s')
    ensures ConcurrentMap.Next(I(s), I(s'))
  {
    InsertCompleteInterpretation(s, s', tid);
    assert ConcurrentMap.InsertEnd(I(s), I(s'), tid);
    assert ConcurrentMap.NextStep(I(s), I(s'),
        ConcurrentMap.InsertEndStep(tid));
  }

  lemma QueryInitStepRefinesNext(s: Variables, s': Variables, key: Key, tid: nat)
    requires Inv(s)
    requires ValidThreadId(s, tid)
    requires ValidThreadId(s', tid)
    requires s'.threads == s.threads[tid := s'.threads[tid]]
    requires QueryInit(s.sv, s'.sv, s.threads[tid], s'.threads[tid], key)
    ensures Inv(s')
    ensures ConcurrentMap.Next(I(s), I(s'))
  {
    assert ConcurrentMap.NextStep(I(s), I(s'),
        ConcurrentMap.QueryStartStep(tid, key));
  }

  lemma QueryAdvanceStepRefinesNext(s: Variables, s': Variables, tid: nat)
    requires Inv(s)
    requires ValidThreadId(s, tid)
    requires ValidThreadId(s', tid)
    requires s'.threads == s.threads[tid := s'.threads[tid]]
    requires QueryAdvance(s.sv, s'.sv, s.threads[tid], s'.threads[tid])
    ensures Inv(s')
    ensures ConcurrentMap.Next(I(s), I(s'))
  {
    assert ConcurrentMap.NextStep(I(s), I(s'), ConcurrentMap.NoOpStep);
  }

  lemma QueryCompleteStepRefinesNext(s: Variables, s': Variables, tid: nat, value: Value)
    requires Inv(s)
    requires ValidThreadId(s, tid)
    requires ValidThreadId(s', tid)
    requires s'.threads == s.threads[tid := s'.threads[tid]]
    requires QueryComplete(s.sv, s'.sv, s.threads[tid], s'.threads[tid], value)
    ensures Inv(s')
    ensures ConcurrentMap.Next(I(s), I(s'))
  {
    PointInterpretationForwards(s.sv.table, s.threads[tid].slot);
    assert ConcurrentMap.NextStep(I(s), I(s'),
        ConcurrentMap.QueryEndStep(tid, Some(value)));
  }

  lemma RefinesNextThread(s: Variables, s': Variables, tid: nat)
    requires Inv(s)
    requires NextThread(s, s', tid)
    ensures Inv(s')
    ensures ConcurrentMap.Next(I(s), I(s'))
  {
    var step: L.Step :| L.NextStep(s.sv, s'.sv, s.threads[tid], s'.threads[tid], step);
    NextPreservesInv(s, s');
    match step {
      case InsertInitStep(key, value)
          => InsertInitStepRefinesNext(s, s', key, value, tid);
      case InsertAdvanceStep
          => InsertAdvanceStepRefinesNext(s, s', tid);
      case InsertCompleteStep
          => InsertCompleteStepRefinesNext(s, s', tid);
      case QueryInitStep(key)
          => QueryInitStepRefinesNext(s, s', key, tid);
      case QueryAdvanceStep
          => QueryAdvanceStepRefinesNext(s, s', tid);
      case QueryCompleteStep(value)
          => QueryCompleteStepRefinesNext(s, s', tid, value);
    }
  }

  lemma RefinesNext(s: Variables, s': Variables)
    requires Inv(s)
    requires Next(s, s')
    ensures Inv(s')
    ensures ConcurrentMap.Next(I(s), I(s'))
  {
    NextPreservesInv(s, s');
    var tid :| NextThread(s, s', tid);
    RefinesNextThread(s, s', tid);
  }
}
