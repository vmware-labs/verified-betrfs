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

  /*predicate Next(s: Variables, s': Variables) {
    Internal(s, s') || (exists id,input :: NewTicket(s, s', id, input))
        || (exists id,input :: ConsumeStub(s, s', id, input))
  }*/

  ////// Invariant

  predicate Complete(table: seq<Option<HT.Info>>)
  {
    && (forall i | 0 <= i < |table| :: table[i].Some?)
  }

  // unwrapped_index
  function adjust(i: int, root: int) : int
  requires 0 <= i < HT.FixedSize()
  requires 0 <= root <= HT.FixedSize()
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
  requires |table| == HT.FixedSize()
  requires Complete(table)
  requires 0 <= e < |table|
  requires 0 <= i < |table|
  {
    // No matter which empty pivot cell 'e' we choose, every entry is 'downstream'
    // of the place that it hashes to.
    // Likewise for insert pointers and others

    table[e].value.entry.Empty? && !table[e].value.state.RemoveTidying? ==> (
      && (table[i].value.entry.Full? ==> (
        var h := HT.hash(table[i].value.entry.kv.key) as int;
        && adjust(h, e+1) <= adjust(i, e+1)
      ))
      && (table[i].value.state.Inserting? ==> (
        var h := HT.hash(table[i].value.state.kv.key) as int;
        && adjust(h, e+1) <= adjust(i, e+1)
      ))
      && ((table[i].value.state.Removing? || table[i].value.state.Querying?) ==> (
        var h := HT.hash(table[i].value.state.key) as int;
        && adjust(h, e+1) <= adjust(i, e+1)
      ))
    )
  }

  // 'Robin Hood' order
  // It's not enough to say that hash(entry[i]) <= hash(entry[i+1])
  // because of wraparound. We do a cyclic comparison 'rooted' at an
  // arbitrary empty element, given by e.
  predicate ValidHashOrdering(table: seq<Option<HT.Info>>, e: int, j: int, k: int)
  requires |table| == HT.FixedSize()
  requires Complete(table)
  requires 0 <= e < |table|
  requires 0 <= j < |table|
  requires 0 <= k < |table|
  {
    (table[e].value.entry.Empty? && !table[e].value.state.RemoveTidying? && table[j].value.entry.Full? && adjust(j, e + 1) < adjust(k, e + 1) ==> (
      var hj := HT.hash(table[j].value.entry.kv.key) as int;

      && (table[k].value.entry.Full? ==> (
        var hk := HT.hash(table[k].value.entry.kv.key) as int;
        && adjust(hj, e + 1) <= adjust(hk, e + 1)
      ))

      // If entry 'k' has an 'Inserting' action on it, then that action must have
      // gotten past entry 'j'.
      && (table[k].value.state.Inserting? ==> (
        var ha := HT.hash(table[k].value.state.kv.key) as int;
        && adjust(hj, e+1) <= adjust(ha, e+1)
      ))

      && ((table[k].value.state.Removing? || table[k].value.state.Querying?) ==> (
        var ha := HT.hash(table[k].value.state.key) as int;
        && adjust(hj, e+1) <= adjust(ha, e+1)
      ))
    ))
  }

  predicate InsertionNotPastKey(table: seq<Option<HT.Info>>, e: int, j: int, k: int)
  requires |table| == HT.FixedSize()
  requires Complete(table)
  requires 0 <= e < |table|
  requires 0 <= j < |table|
  requires 0 <= k < |table|
  {
    (table[e].value.entry.Empty? && !table[e].value.state.RemoveTidying? && table[j].value.entry.Full? && adjust(j, e + 1) < adjust(k, e + 1) ==> (
      // If entry 'k' has an 'Inserting' action on it, then that action must not have
      // gotten past entry 'j'.
      && (table[k].value.state.Inserting? ==> (
        table[k].value.state.kv.key != table[j].value.entry.kv.key
      ))
      && ((table[k].value.state.Removing? || table[k].value.state.Querying?) ==> (
        table[k].value.state.key != table[j].value.entry.kv.key
      ))
    ))
  }

  /*predicate ExistsEmptyEntry(table: seq<Option<HT.Info>>)
  {
    exists e :: 0 <= e < |table| && table[e].Some? && table[e].value.entry.Empty?
        && !table[e].value.state.RemoveTidying?
  }*/

  predicate InvTable(table: seq<Option<HT.Info>>)
  {
    && |table| == HT.FixedSize()
    && Complete(table)
    //&& ExistsEmptyEntry(table)
    && KeysUnique(table)
    && (forall e, i | 0 <= e < |table| && 0 <= i < |table|
        :: ValidHashInSlot(table, e, i))
    && (forall e, j, k | 0 <= e < |table| && 0 <= j < |table| && 0 <= k < |table|
        :: ValidHashOrdering(table, e, j, k))
    && (forall e, j, k | 0 <= e < |table| && 0 <= j < |table| && 0 <= k < |table|
        :: InsertionNotPastKey(table, e, j, k))
  }

  function InfoQuantity(s: Option<HT.Info>) : nat {
    if s.None? then 0 else (
      (if s.value.state.Inserting? then 1 else 0) +
      (if s.value.state.RemoveTidying? || s.value.entry.Full? then 1 else 0)
    )
  }

  function {:opaque} TableQuantity(s: seq<Option<HT.Info>>) : nat {
    if s == [] then 0 else TableQuantity(s[..|s|-1]) + InfoQuantity(s[|s| - 1])
  }

  predicate Inv(s: Variables)
  {
    && s.R?
    && InvTable(s.table)
    && TableQuantity(s.table) + s.insert_capacity == HT.Capacity()
  }

  lemma TableQuantity_replace1(s: seq<Option<HT.Info>>, s': seq<Option<HT.Info>>, i: int)
  requires 0 <= i < |s| == |s'|
  requires forall j | 0 <= j < |s| :: i != j ==> s[j] == s'[j]
  ensures TableQuantity(s') == TableQuantity(s) + InfoQuantity(s'[i]) - InfoQuantity(s[i])
  {
    reveal_TableQuantity();
    if i == |s| - 1 {
      assert s[..|s|-1] == s'[..|s|-1];
    } else {
      TableQuantity_replace1(s[..|s|-1], s'[..|s'|-1], i);
    }
  }

  lemma TableQuantity_replace2(s: seq<Option<HT.Info>>, s': seq<Option<HT.Info>>, i: int)
  requires 0 <= i < |s| == |s'|
  requires |s| > 1
  requires
      var i' := (if i == |s| - 1 then 0 else i + 1);
      forall j | 0 <= j < |s| :: i != j && i' != j ==> s[j] == s'[j]
  ensures
      var i' := (if i == |s| - 1 then 0 else i + 1);
    TableQuantity(s') == TableQuantity(s)
        + InfoQuantity(s'[i]) - InfoQuantity(s[i])
        + InfoQuantity(s'[i']) - InfoQuantity(s[i'])
  {
    var s0 := s[i := s'[i]];
    TableQuantity_replace1(s, s0, i);
    var i' := (if i == |s| - 1 then 0 else i + 1);
    TableQuantity_replace1(s0, s', i');
  }

  function {:opaque} get_empty_cell(table: seq<Option<HT.Info>>) : (e: int)
  requires InvTable(table)
  requires TableQuantity(table) < |table|
  ensures 0 <= e < |table| && table[e].Some? && table[e].value.entry.Empty?
        && !table[e].value.state.RemoveTidying?
  {
    assert exists e' :: 0 <= e' < |table| && table[e'].Some? && table[e'].value.entry.Empty?
        && !table[e'].value.state.RemoveTidying? by {
      var t := get_empty_cell_other_than_insertion_cell_table(table);
    }
    var e' :| 0 <= e' < |table| && table[e'].Some? && table[e'].value.entry.Empty?
        && !table[e'].value.state.RemoveTidying?;
    e'
  }

  lemma get_empty_cell_other_than_insertion_cell_table(table: seq<Option<HT.Info>>)
  returns (e: int)
  requires Complete(table)
  requires TableQuantity(table) < |table|
  ensures 0 <= e < |table| && table[e].Some? && table[e].value.entry.Empty?
        && !table[e].value.state.RemoveTidying?
        && !table[e].value.state.Inserting?
  {
    reveal_TableQuantity();
    e := |table| - 1;
    if table[e].value.entry.Empty?
        && !table[e].value.state.RemoveTidying?
        && !table[e].value.state.Inserting? {
      return;
    } else {
      e := get_empty_cell_other_than_insertion_cell_table(table[..|table| - 1]);
    }
  }

  lemma get_empty_cell_other_than_insertion_cell(s: Variables)
  returns (e: int)
  requires Inv(s)
  ensures 0 <= e < |s.table| && s.table[e].Some? && s.table[e].value.entry.Empty?
        && !s.table[e].value.state.RemoveTidying?
        && !s.table[e].value.state.Inserting?
  {
    e := get_empty_cell_other_than_insertion_cell_table(s.table);
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
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures InsertionNotPastKey(s'.table, e, j, k)
    {
      assert InsertionNotPastKey(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
    }

    var h := HT.hash(insert_ticket.input.key) as int;
    TableQuantity_replace1(s.table, s'.table, h);
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

      //var k' := if k > 0 then k - 1 else |s.table| - 1;

      assert ValidHashInSlot(s.table, e, pos);
      assert ValidHashOrdering(s.table, e, j, pos);
      assert ValidHashOrdering(s.table, e, pos, k);

      /*if j == pos && (pos == HT.FixedSize() - 1 ==> k == 0) && (pos < HT.FixedSize() - 1 ==> k == j + 1) {
        assert ValidHashOrdering(s'.table, e, j, k);
      } else if j == pos {
        assert ValidHashOrdering(s'.table, e, j, k);
      } else if (pos == HT.FixedSize() - 1 ==> k == 0) && (pos < HT.FixedSize() - 1 ==> k == pos + 1) {
        if s'.table[e].value.entry.Empty? && s'.table[j].value.entry.Full? && adjust(j, e) <= adjust(k, e) && s'.table[k].value.state.Inserting? {
          if j == k {
            assert ValidHashOrdering(s'.table, e, j, k);
          } else {
            assert HT.hash(s.table[j].value.entry.kv.key)
                == HT.hash(s'.table[j].value.entry.kv.key);
            assert HT.hash(s.table[pos].value.state.kv.key)
                == HT.hash(s'.table[k].value.state.kv.key);

            assert s.table[e].value.entry.Empty?;
            assert s.table[j].value.entry.Full?;
            assert adjust(j, e) <= adjust(pos, e);
            assert s.table[pos].value.state.Inserting?;

            assert ValidHashOrdering(s.table, e, j, pos);
            assert ValidHashOrdering(s'.table, e, j, k);
          }
        }
      } else {
        assert ValidHashOrdering(s'.table, e, j, k);
      }*/
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures InsertionNotPastKey(s'.table, e, j, k)
    {
      assert InsertionNotPastKey(s.table, e, j, pos);

      assert InsertionNotPastKey(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
    }

    TableQuantity_replace2(s.table, s'.table, pos);
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

      assert ValidHashInSlot(s.table, e, pos);
      assert ValidHashOrdering(s.table, e, j, pos);
      assert ValidHashOrdering(s.table, e, pos, k);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures InsertionNotPastKey(s'.table, e, j, k)
    {
      assert InsertionNotPastKey(s.table, e, j, pos);

      assert InsertionNotPastKey(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);

      assert ValidHashOrdering(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, pos);
      assert ValidHashOrdering(s.table, e, j, pos);
    }

    forall i | 0 <= i < |s.table| && s.table[i].value.entry.Full?
    ensures s.table[i].value.entry.kv.key != s.table[pos].value.state.kv.key
    {
      //var e :| 0 <= e < |s.table| && s.table[e].value.entry.Empty?
      //  && !s.table[e].value.state.RemoveTidying?;
      var e := get_empty_cell_other_than_insertion_cell(s);
      assert InsertionNotPastKey(s.table, e, i, pos);
      //assert ValidHashInSlot(s.table, e, i);
      assert ValidHashInSlot(s.table, e, pos);
      assert ValidHashOrdering(s.table, e, pos, i);
      //assert ValidHashOrdering(s.table, e, i, pos);
    }

    TableQuantity_replace2(s.table, s'.table, pos);
  }

  lemma InsertDone_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.InsertDone(s, s', pos)
  ensures Inv(s')
  {
    forall e, i | 0 <= i < |s'.table| && 0 <= e < |s'.table|
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
      //assert ValidHashInSlot(s.table, e, pos);
      //assert ValidHashOrdering(s.table, e, j, pos);
      //assert ValidHashOrdering(s.table, e, pos, k);

      //assert InsertionNotPastKey(s.table, e, j, pos);

      //assert InsertionNotPastKey(s.table, pos, j, k);
      //assert InsertionNotPastKey(s.table, pos, k, j);

      //assert ValidHashOrdering(s.table, pos, j, k);
      //assert ValidHashOrdering(s.table, pos, k, j);

      //assert ValidHashInSlot(s.table, pos, j);
      assert ValidHashInSlot(s.table, pos, k);
    }

    /*assert ExistsEmptyEntry(s'.table) by {
      var e' := get_empty_cell_other_than_insertion_cell(s);
      assert 0 <= e' < |s'.table| && s'.table[e'].Some? && s'.table[e'].value.entry.Empty?
            && !s'.table[e'].value.state.RemoveTidying?;
    }*/

    forall i | 0 <= i < |s.table| && s.table[i].value.entry.Full?
    ensures s.table[i].value.entry.kv.key != s.table[pos].value.state.kv.key
    {
      //var e :| 0 <= e < |s.table| && s'.table[e].value.entry.Empty?
        //&& !s.table[e].value.state.RemoveTidying?;
      var e := get_empty_cell_other_than_insertion_cell(s);
      assert InsertionNotPastKey(s.table, e, i, pos);
      //assert InsertionNotPastKey(s.table, e, pos, i);
      assert ValidHashInSlot(s.table, e, pos);
      //assert ValidHashInSlot(s.table, e, i);
      //assert ValidHashOrdering(s.table, e, pos, i);
      //assert ValidHashOrdering(s.table, e, i, pos);

      //assert InsertionNotPastKey(s.table, pos, i, pos);
      //assert InsertionNotPastKey(s.table, pos, pos, i);
      //assert ValidHashInSlot(s.table, pos, pos);
      assert ValidHashInSlot(s.table, pos, i);
      //assert ValidHashOrdering(s.table, pos, pos, i);
      //assert ValidHashOrdering(s.table, pos, i, pos);
    }

    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures InsertionNotPastKey(s'.table, e, j, k)
    {
      assert InsertionNotPastKey(s.table, e, j, k);

      //assert InsertionNotPastKey(s.table, e, j, pos);
      //assert InsertionNotPastKey(s.table, e, k, pos);
      //assert InsertionNotPastKey(s.table, e, pos, j);
      //assert InsertionNotPastKey(s.table, e, pos, k);
      //assert InsertionNotPastKey(s.table, e, j, k);
      //assert InsertionNotPastKey(s.table, e, k, j);
      //assert ValidHashInSlot(s.table, e, pos);
      assert ValidHashInSlot(s.table, e, j);
      //assert ValidHashInSlot(s.table, e, k);
      //assert ValidHashOrdering(s.table, e, pos, j);
      //assert ValidHashOrdering(s.table, e, j, pos);
      //assert ValidHashOrdering(s.table, e, pos, k);
      //assert ValidHashOrdering(s.table, e, k, pos);
      //assert ValidHashOrdering(s.table, e, j, k);
      //assert ValidHashOrdering(s.table, e, k, j);

      //assert InsertionNotPastKey(s.table, pos, j, pos);
      //assert InsertionNotPastKey(s.table, pos, pos, j);
      //assert InsertionNotPastKey(s.table, pos, k, pos);
      //assert InsertionNotPastKey(s.table, pos, pos, k);
      //assert InsertionNotPastKey(s.table, pos, k, j);
      //assert InsertionNotPastKey(s.table, pos, j, k);
      //assert ValidHashInSlot(s.table, pos, pos);
      //assert ValidHashInSlot(s.table, pos, j);
      assert ValidHashInSlot(s.table, pos, k);
      //assert ValidHashOrdering(s.table, pos, pos, j);
      //assert ValidHashOrdering(s.table, pos, j, pos);
      //assert ValidHashOrdering(s.table, pos, pos, k);
      //assert ValidHashOrdering(s.table, pos, k, pos);
      //assert ValidHashOrdering(s.table, pos, j, k);
      //assert ValidHashOrdering(s.table, pos, k, j);

    }

    TableQuantity_replace1(s.table, s'.table, pos);
  }

  lemma InsertUpdate_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.InsertUpdate(s, s', pos)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: s.table[i].value.entry.Empty? ==> s'.table[i].value.entry.Empty?;

    forall e, i | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures InsertionNotPastKey(s'.table, e, j, k)
    {
      assert InsertionNotPastKey(s.table, e, j, k);
    }

    TableQuantity_replace1(s.table, s'.table, pos);
  }

  lemma ProcessQueryTicket_PreservesInv(s: Variables, s': Variables, query_ticket: HT.Ticket)
  requires Inv(s)
  requires HT.ProcessQueryTicket(s, s', query_ticket)
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
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures InsertionNotPastKey(s'.table, e, j, k)
    {
      assert InsertionNotPastKey(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
    }

    var h := HT.hash(query_ticket.input.key) as int;
    TableQuantity_replace1(s.table, s'.table, h);
  }

  lemma QuerySkip_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.QuerySkip(s, s', pos)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: s'.table[i].value.entry == s.table[i].value.entry;

    forall i, e | 0 <= i < |s'.table| && 0 <= e < |s'.table|
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
      assert ValidHashInSlot(s.table, e, pos);
      assert ValidHashOrdering(s.table, e, j, pos);
      assert ValidHashOrdering(s.table, e, pos, k);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures InsertionNotPastKey(s'.table, e, j, k)
    {
      assert InsertionNotPastKey(s.table, e, j, pos);
      assert InsertionNotPastKey(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
    }

    TableQuantity_replace2(s.table, s'.table, pos);
  }

  lemma QueryDone_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.QueryDone(s, s', pos)
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
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures InsertionNotPastKey(s'.table, e, j, k)
    {
      assert InsertionNotPastKey(s.table, e, j, k);
    }

    TableQuantity_replace2(s.table, s'.table, pos);
  }

  lemma QueryNotFound_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.QueryNotFound(s, s', pos)
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
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures InsertionNotPastKey(s'.table, e, j, k)
    {
      assert InsertionNotPastKey(s.table, e, j, k);
    }

    TableQuantity_replace2(s.table, s'.table, pos);
  }

  lemma ProcessRemoveTicket_PreservesInv(s: Variables, s': Variables, remove_ticket: HT.Ticket)
  requires Inv(s)
  requires HT.ProcessRemoveTicket(s, s', remove_ticket)
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
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures InsertionNotPastKey(s'.table, e, j, k)
    {
      assert InsertionNotPastKey(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
    }

    var h := HT.hash(remove_ticket.input.key) as int;
    TableQuantity_replace1(s.table, s'.table, h);
  }

  lemma RemoveSkip_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.RemoveSkip(s, s', pos)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: s'.table[i].value.entry == s.table[i].value.entry;

    forall i, e | 0 <= i < |s'.table| && 0 <= e < |s'.table|
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
      assert ValidHashInSlot(s.table, e, pos);
      assert ValidHashOrdering(s.table, e, j, pos);
      assert ValidHashOrdering(s.table, e, pos, k);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures InsertionNotPastKey(s'.table, e, j, k)
    {
      assert InsertionNotPastKey(s.table, e, j, pos);
      assert InsertionNotPastKey(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
    }

    TableQuantity_replace2(s.table, s'.table, pos);
  }

  lemma RemoveFoundIt_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.RemoveFoundIt(s, s', pos)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: i != pos ==> s'.table[i].value.entry == s.table[i].value.entry;

    forall i, e | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures InsertionNotPastKey(s'.table, e, j, k)
    {
      assert InsertionNotPastKey(s.table, e, j, k);
    }

    TableQuantity_replace2(s.table, s'.table, pos);
  }

  lemma RemoveNotFound_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.RemoveNotFound(s, s', pos)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: i != pos ==> s'.table[i].value.entry == s.table[i].value.entry;

    forall i, e | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures InsertionNotPastKey(s'.table, e, j, k)
    {
      assert InsertionNotPastKey(s.table, e, j, k);
    }

    TableQuantity_replace2(s.table, s'.table, pos);
  }

  lemma RemoveTidy_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.RemoveTidy(s, s', pos)
  ensures Inv(s')
  {
    /*assert ExistsEmptyEntry(s'.table) by {
      var e :| 0 <= e < |s.table| && s.table[e].Some? && s.table[e].value.entry.Empty?
        && !s.table[e].value.state.RemoveTidying?;
      assert 0 <= e < |s'.table| && s'.table[e].Some? && s'.table[e].value.entry.Empty?
        && !s'.table[e].value.state.RemoveTidying?;
    }*/

    var pos' := if pos < |s.table| - 1 then pos + 1 else 0;

    forall i, e | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);
      assert ValidHashInSlot(s.table, e, pos');
      //assert ValidHashOrdering(s.table, e, pos, pos');
      /*if i == pos {
        if s'.table[e].value.entry.Empty? && !s'.table[e].value.state.RemoveTidying?
            && s'.table[i].value.entry.Full? && s.table[pos'].value.entry.Full? {
          var h := HT.hash(s'.table[i].value.entry.kv.key) as int;
          assert h == HT.hash(s.table[pos'].value.entry.kv.key) as int;

          assert e < h <= pos'
           || h <= pos' < e
           || pos' < e < h;

          assert h != pos';

          assert e < h <= pos
           || h <= pos < e
           || pos < e < h;

          assert ValidHashInSlot(s'.table, e, i);
        }

        assert ValidHashInSlot(s'.table, e, i);
      } else {
        assert ValidHashInSlot(s'.table, e, i);
      }*/
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
      assert ValidHashOrdering(s.table, e, pos', k);
      assert ValidHashOrdering(s.table, e, j, pos');
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures InsertionNotPastKey(s'.table, e, j, k)
    {
      assert InsertionNotPastKey(s.table, e, j, k);
      assert InsertionNotPastKey(s.table, e, pos', k);
      assert InsertionNotPastKey(s.table, e, j, pos');
    }

    TableQuantity_replace2(s.table, s'.table, pos);
  }

  lemma RemoveDone_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.RemoveDone(s, s', pos)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: s'.table[i].value.entry == s.table[i].value.entry;

    var pos' := if pos < |s.table| - 1 then pos + 1 else 0;

    assert s'.table[pos].value.entry.Empty?;

    forall i, e | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      var e' := get_empty_cell(s.table);
      
      assert ValidHashInSlot(s.table, e, i);

      assert ValidHashInSlot(s.table, pos', i);
      assert ValidHashOrdering(s.table, e', pos', i);

      assert ValidHashInSlot(s.table, e', i);

      assert ValidHashInSlot(s.table, i, e');

      //assert ValidHashInSlot(s.table, e', pos');
      //assert ValidHashInSlot(s.table, pos', e');

      //assert ValidHashInSlot(s.table, i, e);
      //assert ValidHashOrdering(s.table, e', i, pos');
      //assert ValidHashInSlot(s.table, pos, i);
      //assert ValidHashOrdering(s.table, e', pos, i);
      //assert ValidHashOrdering(s.table, e', i, pos);

      /*var e1 := if e < |s.table| - 1 then e + 1 else 0;
 
      assert ValidHashInSlot(s.table, e1, i);

      assert ValidHashInSlot(s.table, pos', i);
      assert ValidHashOrdering(s.table, e1, pos', i);

      assert ValidHashInSlot(s.table, e1, i);

      assert ValidHashInSlot(s.table, i, e1);

      assert ValidHashInSlot(s.table, e1, pos');
      assert ValidHashInSlot(s.table, pos', e1);

      assert ValidHashInSlot(s.table, i, e);
      assert ValidHashOrdering(s.table, e1, i, pos');
      assert ValidHashInSlot(s.table, pos, i);
      assert ValidHashOrdering(s.table, e1, pos, i);
      assert ValidHashOrdering(s.table, e1, i, pos);

      assert ValidHashOrdering(s.table, e1, i, e);
      assert ValidHashOrdering(s.table, e1, e, i);
      assert ValidHashInSlot(s.table, e1, i);

      assert ValidHashOrdering(s.table, e', e, e1);

      assert ValidHashOrdering(s.table, e', e1, i);
      assert ValidHashInSlot(s.table, e', e1);

      assert ValidHashInSlot(s.table, e, e);
      assert ValidHashInSlot(s.table, e', e');
      assert ValidHashInSlot(s.table, e1, e1);

      assert ValidHashInSlot(s.table, e', i);

      assert ValidHashOrdering(s.table, e', e, i);*/


      /*if e == pos {
        if i == pos' {
          assert ValidHashInSlot(s'.table, e, i);
        } else {
          if s.table[pos'].value.entry.Full? {
            if adjust(i, pos) < adjust(e', pos) {
              assert ValidHashInSlot(s'.table, e, i);
            } else if i == e' {
              assert s.table[e1].value.entry.Full?  ==>
                  HT.hash(s.table[e1].value.entry.kv.key) as int
                == e1;
              
              if s.table[e1].value.entry.Full? {
                if e == e' {
                  assert ValidHashInSlot(s'.table, e, i);
                } else {
                  assert ValidHashInSlot(s'.table, e, i);
                }
              } else {
                assert ValidHashInSlot(s'.table, e, i);
              }
            } else {
              assert ValidHashInSlot(s'.table, e, i);
            }
          } else {
            assert ValidHashInSlot(s'.table, e, i);
          }
        }
      } else {
        assert ValidHashInSlot(s'.table, e, i);
      }*/
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      var e' := get_empty_cell(s.table);

      assert ValidHashOrdering(s.table, e, j, k);

      assert ValidHashOrdering(s.table, e', j, k);
      //assert ValidHashOrdering(s.table, e', k, j);

      assert ValidHashInSlot(s.table, pos', j);
      assert ValidHashOrdering(s.table, e', pos', j);
      //assert ValidHashInSlot(s.table, e', j);

      //assert ValidHashInSlot(s.table, pos', k);
      //assert ValidHashOrdering(s.table, e', pos', k);
      assert ValidHashInSlot(s.table, e', k);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures InsertionNotPastKey(s'.table, e, j, k)
    {
      var e' := get_empty_cell(s.table);

      assert InsertionNotPastKey(s.table, e, j, k);

      //assert ValidHashOrdering(s.table, e, j, k);
      //assert ValidHashOrdering(s.table, e', j, k);
      assert ValidHashInSlot(s.table, pos', j);
      assert ValidHashOrdering(s.table, e', pos', j);
      assert ValidHashInSlot(s.table, e', k);

      //assert InsertionNotPastKey(s.table, e, j, k);
      assert InsertionNotPastKey(s.table, e', j, k);
      //assert InsertionNotPastKey(s.table, e', pos', j);
    }

    TableQuantity_replace2(s.table, s'.table, pos);
  }

  lemma UpdateStep_PreservesInv(s: Variables, s': Variables, step: HT.Step)
  requires Inv(s)
  requires HT.UpdateStep(s, s', step)
  ensures Inv(s')
  {
    match step {
      case ProcessInsertTicketStep(insert_ticket) => ProcessInsertTicket_PreservesInv(s, s', insert_ticket);
      case InsertSkipStep(pos) => InsertSkip_PreservesInv(s, s', pos);
      case InsertSwapStep(pos) => InsertSwap_PreservesInv(s, s', pos);
      case InsertDoneStep(pos) => InsertDone_PreservesInv(s, s', pos);
      case InsertUpdateStep(pos) => InsertUpdate_PreservesInv(s, s', pos);

      case ProcessRemoveTicketStep(remove_ticket) => ProcessRemoveTicket_PreservesInv(s, s', remove_ticket);
      case RemoveSkipStep(pos) => RemoveSkip_PreservesInv(s, s', pos);
      case RemoveFoundItStep(pos) => RemoveFoundIt_PreservesInv(s, s', pos);
      case RemoveNotFoundStep(pos) => RemoveNotFound_PreservesInv(s, s', pos);
      case RemoveTidyStep(pos) => RemoveTidy_PreservesInv(s, s', pos);
      case RemoveDoneStep(pos) => RemoveDone_PreservesInv(s, s', pos);

      case ProcessQueryTicketStep(query_ticket) => ProcessQueryTicket_PreservesInv(s, s', query_ticket);
      case QuerySkipStep(pos) => QuerySkip_PreservesInv(s, s', pos);
      case QueryDoneStep(pos) => QueryDone_PreservesInv(s, s', pos);
      case QueryNotFoundStep(pos) => QueryNotFound_PreservesInv(s, s', pos);
    }
  }


  lemma Update_PreservesInv(s: Variables, s': Variables)
  requires Inv(s)
  requires HT.Update(s, s')
  ensures Inv(s')
  {
    var step :| HT.UpdateStep(s, s', step);
    UpdateStep_PreservesInv(s, s', step);
  }
}
