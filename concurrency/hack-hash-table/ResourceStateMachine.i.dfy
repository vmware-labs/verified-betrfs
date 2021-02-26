include "HTResource.i.dfy"

module ResourceStateMachine {
  import opened KeyValueType
  import opened Options

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
    s' == HT.add(s, HT.input_ticket(id, input))
  }

  predicate ConsumeStub(s: Variables, s': Variables, id: int, output: MapIfc.Output)
  {
    s == HT.add(s', HT.output_stub(id, output))
  }

  ////// Invariant

  predicate Complete(table: seq<Option<HT.Info>>)
  {
    && (forall i | 0 <= i < |table| :: table[i].Some?)
  }

  function adjust(i: int, root: int) : int
  {
    if i < root then HT.FixedSize() + i else i
  }

  // Keys are unique, although we don't count entries being removed
  predicate KeysUnique(table: seq<Option<HT.Info>>)
  requires Complete(table)
  {
    forall i, j | 0 <= i < |table| && 0 <= j < |table| && i != j
      && table[i].value.entry.Full? && table[j].value.entry.Full?
      && !table[i].value.state.RemoveTidying? && !table[j].value.state.RemoveTidying?
        :: table[i].value.entry.kv.key != table[j].value.entry.kv.key
  }

  // If there's an entry in slot `i` with hash `h`, then
  // you must be able to get from `h` to `i` (possibly wrapping around)
  // with passing a free space.
  /*predicate ValidHashInSlot(table: seq<Option<HT.Info>>, i: int)
  requires Complete(table)
  requires 0 <= i < |table|
  {
    table[i].value.entry.Full? ==> (
      var h := HT.hash(table[i].value.entry.kv.key) as int;
      && (h <= i ==> (forall j | h <= j <= i :: table[j].value.entry.Full?))
      && (h > i ==>
        && h < |table|
        && (forall j | 0 <= j <= i :: table[j].value.entry.Full?)
        && (forall j | h <= j < |table| :: table[j].value.entry.Full?)
      )
    )
  }*/

  predicate ValidHashInSlot(table: seq<Option<HT.Info>>, e: int, i: int)
  requires Complete(table)
  requires 0 <= e < |table|
  requires 0 <= i < |table|
  {
    table[e].value.entry.Empty? && table[i].value.entry.Full? ==> (
      var h := HT.hash(table[i].value.entry.kv.key) as int;
      && (
        || e < h <= i
        || h <= i < e
        || i < e < h
      )
      && (table[i].value.state.Inserting? ==> (
        var ha := HT.hash(table[i].value.state.kv.key) as int;
        && (
          || e < ha <= i
          || ha <= i < e
          || i < e < ha
        )
      ))
    )
  }

  // 'Robin Hood' order
  // It's not enough to say that hash(entry[i]) <= hash(entry[i+1])
  // because of wraparound. We do a cyclic comparison 'rooted' at an
  // arbitrary empty element, given by e.
  predicate ValidHashOrdering(table: seq<Option<HT.Info>>, e: int, j: int, k: int)
  requires Complete(table)
  requires 0 <= e < |table|
  requires 0 <= j < |table|
  requires 0 <= k < |table|
  {
    (table[e].value.entry.Empty? && table[j].value.entry.Full? && table[k].value.entry.Full? ==> (
      var hj := HT.hash(table[j].value.entry.kv.key) as int;
      var hk := HT.hash(table[k].value.entry.kv.key) as int;
      && adjust(hj, e) <= adjust(hk, e)

      // If entry 'k' has an 'Inserting' action on it, then that action must have
      // gotten past entry 'j'.
      && (table[k].value.state.Inserting? ==>
        var ha := HT.hash(table[k].value.state.kv.key) as int;
        && adjust(hj, e) <= adjust(ha, e)
      )
    ))
  }

  predicate ExistsEmptyEntry(table: seq<Option<HT.Info>>)
  {
    exists i :: 0 <= i < |table| && table[i].Some? && table[i].value.entry.Empty?
  }

  predicate Inv(s: Variables)
  {
    && s.R?
    && Complete(s.table)
    && ExistsEmptyEntry(s.table)
    && KeysUnique(s.table)
    && (forall e, i | 0 <= e < |s.table| && 0 <= i < |s.table|
        :: ValidHashInSlot(s.table, e, i))
    && (forall e, j, k | 0 <= e < |s.table| && 0 <= j < |s.table| && 0 <= k < |s.table|
        :: ValidHashOrdering(s.table, e, j, k))
  }

  lemma ProcessInsertTicket_PreservesInv(s: Variables, s': Variables, insert_ticket: HT.Ticket)
  requires Inv(s)
  requires HT.ProcessInsertTicket(s, s', insert_ticket)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: s'.table[i].value.entry == s.table[i].value.entry;
    forall i, e | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
      assert ValidHashInSlot(s.table, e, k);
    }
  }

  lemma InsertSkip_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.InsertSkip(s, s', pos)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: s'.table[i].value.entry == s.table[i].value.entry;
    forall e, i | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);

      var i' := if i > 0 then i - 1 else |s.table| - 1;
      assert ValidHashInSlot(s.table, e, i');
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
      assert ValidHashInSlot(s.table, e, k);

      var k' := if k > 0 then k - 1 else |s.table| - 1;

      assert ValidHashInSlot(s.table, e, k');
      assert ValidHashOrdering(s.table, e, k, k');
    }
  }

  lemma InsertSwap_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.InsertSwap(s, s', pos)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: s.table[i].value.entry.Empty? ==> s'.table[i].value.entry.Empty?;
    forall e, i | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);

      var i' := if i > 0 then i - 1 else |s.table| - 1;
      assert ValidHashInSlot(s.table, e, i');
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
      assert ValidHashInSlot(s.table, e, k);

      var k' := if k > 0 then k - 1 else |s.table| - 1;

      assert ValidHashInSlot(s.table, e, k');
      assert ValidHashOrdering(s.table, e, k, k');
    }
  }

}
