include "../../../lib/Base/sequences.i.dfy"
include "../../../lib/Base/Option.s.dfy"
include "CircularRange.i.dfy"

module CircularTable {
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import opened KeyValueType
  import opened Limits
  import opened CircularRange

  function method hash(key: Key) : Index

  function DummyKey() : Key

  datatype Entry =
    | Full(key: Key, value: Value)
    | Empty
  {
    function method Hash(): Index
      requires Full?
    {
      hash(key)
    }

    function method EntryPSL(i: Index): nat
      requires Full?
    {
      PSL(key, i)
    }

    predicate method WithOtherKey(key': Key)
    {
      && Full?
      && key != key'
    }

    predicate method WithKey(key': Key)
    {
      && Full?
      && key == key'
    }

    predicate method ShouldSkip(i: Index, key': Key)
    {
      && WithOtherKey(key')
      && EntryPSL(i) >= PSL(key', i)
    }

    predicate method ShouldSwap(i: Index, key': Key)
    {
      && WithOtherKey(key')
      && EntryPSL(i) < PSL(key', i)
    }
  }

  type Table = seq<Option<Entry>>

  type FixedTable = t: Table
    | |t| == FixedSize() witness *
    
  predicate Complete(table: Table)
  {
    forall i: nat | i < |table| :: table[i].Some?
  }

  function UnitTable(): Table
  {
    seq(FixedSize(), i => None)
  }

  function EmptyTable(): Table
  {
    seq(FixedSize(), i => Some(Empty))
  }

//////////////////////////////////////////////////////////////////////////////
// entry/range predicates
//////////////////////////////////////////////////////////////////////////////

  // PSL == Probe Sequence Length: the probe length from hash(key)
  // to index i
  function method PSL(key: Key, i: Index): nat
  {
    var h := hash(key);
    WrappedDistance(h, i)
  }

  predicate SlotFull(entry: Option<Entry>)
  {
    entry.Some? && entry.value.Full?
  }

  predicate RangeFull(table: FixedTable, range: Range)
  {
    forall i: Index | range.Contains(i) :: SlotFull(table[i])
  }

  function SlotKeyHash(entry: Option<Entry>): Index
    requires SlotFull(entry)
  {
    entry.value.Hash()
  }

  // What's the Probe Sequence Length for the key at this location?
  function method SlotPSL(table: FixedTable, i: Index): nat
    requires SlotFull(table[i])
  {
    table[i].value.EntryPSL(i)
  }

  predicate SlotEmpty(entry: Option<Entry>)
  {
    entry.Some? && entry.value.Empty?
  }

  predicate SlotFullWithOtherKey(entry: Option<Entry>, key: Key)
  {
    && SlotFull(entry)
    && entry.value.WithOtherKey(key)
  }

  predicate RangeFullWithOtherKeys(table: FixedTable, range: Range, key: Key)
  {
    forall i: Index | range.Contains(i) :: SlotFullWithOtherKey(table[i], key)
  }

  predicate SlotShouldSkip(entry: Option<Entry>, i: Index, key: Key)
  {
    && SlotFullWithOtherKey(entry, key)
    // the psl at the slot is geq than the psl of insert
    && entry.value.ShouldSkip(i, key)
  }

  predicate SlotShouldSwap(entry: Option<Entry>, i: Index, key: Key)
  {
    && SlotFullWithOtherKey(entry, key)
    // the psl at the slot is less than the psl of the insert
    && entry.value.ShouldSwap(i, key)
  }

  predicate SlotShouldTidy(entry: Option<Entry>, i: Index)
  {
    && SlotFull(entry)
    && entry.value.Hash() != i
  }

  predicate ValidTidyRange(table: FixedTable, r: Range, key: Key)
  {
    && r.Partial?
    // remove at start
    && SlotFull(table[r.start])
    && table[r.start].value.key == key
    // shift in between
    && (forall i: Index | r.RightShift1().Contains(i)
      :: SlotShouldTidy(table[i], i))
    // leave end's next
    && !SlotShouldTidy(table[NextIndex(r.end)], NextIndex(r.end))
  }

  lemma TidyRangeSufficient(table: FixedTable, r: Range, key: Key)
    requires TableInv(table)
    requires exists e: Index :: SlotEmpty(table[e])
    requires ValidTidyRange(table, r, key)
    ensures var end_next := NextIndex(r.end);
      table[end_next].value.Full? ==>
      SlotKeyHash(table[end_next]) != SlotKeyHash(table[r.end])
  {
    var Partial(start, end) := r;
    var end_next := NextIndex(end);

    if table[end_next].value.Empty? {
      return;
    }

    var h := SlotKeyHash(table[end_next]);
    // assert h == end;

    if SlotKeyHash(table[end]) == h {
      var e : Index :| SlotEmpty(table[e]);
      assert ValidPSL(table, end);
      var h_range := GetHashSegment(table, h);
      assert h_range.Contains(e);
      assert false;
    }
  }

  predicate ValidPartialProbeRange(table: FixedTable, key: Key, range: Range)
  {
    && range.Partial?
    && range.start == hash(key)
    && (forall i: Index | range.Contains(i)
      :: SlotShouldSkip(table[i], i, key))
  }

  predicate KeyPresentProbeRange(table: FixedTable, key: Key, range: Range)
  {
    && ValidPartialProbeRange(table, key, range)
    && SlotFullWithKey(table[range.end], key)
  }

  predicate KeyAbsentProbeRange(table: FixedTable, key: Key, range: Range)
  {
    // skip upto (not including) end
    && ValidPartialProbeRange(table, key, range)
    // insert at start
    && var end := range.end;
    && (SlotShouldSwap(table[end], end, key)
      || SlotEmpty(table[end]))
  }

  // a valid probe range would cover key's hash segment 
  lemma ProbeRangeSufficient(table: FixedTable, key: Key, p_range: Range)
    requires TableInv(table)
    requires KeyAbsentProbeRange(table, key, p_range)
    ensures var h_range := GetHashSegment(table, hash(key));
      h_range.HasSome() ==> (
        && p_range.Contains(h_range.start)
        && p_range.end == h_range.end)
    ensures !TableContainsKey(table, key)
  {
    var h := hash(key);
    var end := p_range.end;

    // the segment that shares the hash
    var h_range := GetHashSegment(table, h);

    if h_range.HasNone() {
      return;
    }

    var Partial(hr_start, hr_end) := h_range;

    // narrow where hr_start is
    assert p_range.Contains(hr_start) by {
      assert ValidPSL(table, hr_start);
    }

    // narrow where hr_end is
    if !(p_range.Contains(hr_end) || hr_end == end) {
      assert h_range.Contains(end);
      assert false;
    }

    // fix where hr_end is
    if p_range.Contains(hr_end) {
      assert ValidPSL(table, hr_end);
      assert false;
    }

    assert hr_end == end;
    assert p_range.Contains(hr_start);

    if exists i: Index ::
      SlotFull(table[i]) && table[i].value.key == key {
      assert false;
    }
  }

  function GetSlotProbeRange(table: FixedTable, i: Index) : Range
    requires SlotFull(table[i])
  {
    Partial(SlotKeyHash(table[i]), i)
  }

  // function GetSubTable(table: FixedTable, range: Range): Table
  //   decreases WrappedDistance(range.start, range.end)
  // {
  //   var Partial(start, end) := range;
  //   if start == end then
  //     []
  //   else
  //     GetSubTable(table, range.RightShrink1()) + [table[end]]
  // }

  predicate RangeEquivalent(t1: FixedTable, t2: FixedTable, range: Range)
  {
    forall i: Index :: range.Contains(i) ==> t1[i] == t2[i]
  }

  predicate RangeKnown(table: FixedTable, range: Range)
  {
    forall i: Index | range.Contains(i) :: table[i].Some?
  }

//////////////////////////////////////////////////////////////////////////////
// robinhood invarints
//////////////////////////////////////////////////////////////////////////////

  // Keys are unique, although we don't count entries being removed
  predicate KeysUnique(table: Table)
    requires Complete(table)
  {
    forall i: nat, j: nat | 
        && i < |table|
        && j < |table|
        && i != j
        && table[i].value.Full?
        && table[j].value.Full?
      :: table[i].value.key != table[j].value.key
  }

  // A hash segment is a contiguous Range in which all the stored keys share
  // the same hash.
  predicate ValidHashSegment(table: FixedTable, hash: Index, range: Range)
    requires Complete(table)
  {
    && range.Partial?
    // // if the segment is Partial, the hash cannot be in the middle 
    // && !Contains(Partial(NextIndex(range.start), range.end), hash))
    // all the keys in the segment share the hash
    && (forall i: Index | range.Contains(i) ::
        && table[i].value.Full?
        && SlotKeyHash(table[i]) == hash)
    // and no where else
    && (forall i: Index | !range.Contains(i) ::
        (table[i].value.Full? ==> 
        SlotKeyHash(table[i]) != hash))
  }

  predicate ExistsHashSegment(table: FixedTable, hash: Index)
    requires Complete(table)
  {
    // there exists a segment of slots that has the matching hash (could be empty)
    exists range: Range :: ValidHashSegment(table, hash, range)
  }

  predicate ValidPSL(table: FixedTable, i: Index)
    requires Complete(table)
  {
    table[i].value.Full? ==>
    (
      var key := table[i].value.key;
      var h_i := hash(key);
      forall j: Index :: Partial(h_i, i).Contains(j) ==> 
      (
        && table[j].value.Full?
        && SlotPSL(table, j) >= PSL(key, j)
      )
    )
  }

  predicate TableWF(table: Table)
  {
    && Complete(table)
    && KeysUnique(table)
  }

  predicate TableInv(table: FixedTable)
  {
    && TableWF(table)
    // && (exists e: Index :: SlotEmpty(table[e]))
    // && (forall h: Index :: ValidOrdering(table, h))
    && (forall i: Index ::
      && ValidPSL(table, i)
      && ExistsHashSegment(table, i))
  }

  function GetHashSegment(table: FixedTable, hash: Index): (r: Range)
    requires TableInv(table)
    ensures ValidHashSegment(table, hash, r)
  {
    assert ExistsHashSegment(table, hash);
    var range: Range :|
      ValidHashSegment(table, hash, range);
    range
  }

//////////////////////////////////////////////////////////////////////////////
// quantity 
//////////////////////////////////////////////////////////////////////////////

  function EntryQuantity(entry: Option<Entry>): nat
  {
    if entry.Some? && entry.value.Full? then 1 else 0
  }

  function {:opaque} TableQuantity(s: Table) : nat
  {
    if s == [] then
      0
    else
      (TableQuantity(s[..|s| - 1]) + EntryQuantity(Last(s)))
  }

  lemma FullTableQuantity(table: Table)
    requires forall i: int :: 
      0 <= i < |table| ==> (table[i].Some? && table[i].value.Full?)
    ensures TableQuantity(table) == |table|
  {
    reveal TableQuantity();
  }

  lemma EmptyTableQuantity(table: Table)
    requires forall i : int ::
      0 <= i < |table| ==> table[i] == Some(Empty)
    ensures TableQuantity(table) == 0
  {
    reveal TableQuantity();
  }

  lemma TableQuantityReplace1(t: Table, t': Table, i: Index)
    requires 0 <= i < |t| == |t'|
    requires forall j | 0 <= j < |t| :: i != j ==> t[j] == t'[j]
    ensures TableQuantity(t') == TableQuantity(t) + EntryQuantity(t'[i]) - EntryQuantity(t[i])
  {
    reveal_TableQuantity();
    var end := |t| - 1;
    if i == end {
      assert t[..end] == t'[..end];
    } else {
      TableQuantityReplace1(t[..end], t'[..end], i);
    }
  }

  lemma TableQuantityConcat(t1: Table, t2: Table)
    decreases |t2|
    ensures TableQuantity(t1) + TableQuantity(t2) == TableQuantity(t1 + t2)
  {
    var t := t1 + t2;

    if |t1| == 0 || |t2| == 0 {
      assert t == if |t1| == 0 then t2 else t1;
      reveal TableQuantity();
      return;
    }

    calc == {
      TableQuantity(t);
      {
        reveal TableQuantity();
      }
      TableQuantity(t[..|t| - 1]) + EntryQuantity(Last(t));
      {
        assert Last(t) == Last(t2);
      }
      TableQuantity(t[..|t| - 1]) + EntryQuantity(Last(t2));
      TableQuantity((t1 + t2)[..|t| - 1]) + EntryQuantity(Last(t2));
      {
        assert (t1 + t2)[..|t| - 1] == t1 + t2[..|t2| - 1];
      }
      TableQuantity(t1 + t2[..|t2| - 1]) + EntryQuantity(Last(t2));
      {
        TableQuantityConcat(t1, t2[..|t2| - 1]);
      }
      TableQuantity(t1) +  TableQuantity(t2[..|t2| - 1]) + EntryQuantity(Last(t2));
      {
        reveal TableQuantity();
      }
      TableQuantity(t1) +  TableQuantity(t2);
    }
  }

  lemma TableQuantityConcat4(t1: Table, t2: Table, t3: Table, t4: Table)
    ensures 
      TableQuantity(t1 + t2 + t3 + t4)
        == 
      TableQuantity(t1) + TableQuantity(t2) + TableQuantity(t3) + TableQuantity(t4);
  {
      TableQuantityConcat(t1 + t2 + t3, t4);
      TableQuantityConcat(t1 + t2, t3);
      TableQuantityConcat(t1, t2);
  }

  lemma TableQuantityConcat5(t1: Table, t2: Table, t3: Table, t4: Table, t5: Table)
    ensures 
      TableQuantity(t1 + t2 + t3 + t4 + t5)
        == 
      TableQuantity(t1) + TableQuantity(t2) + TableQuantity(t3) + TableQuantity(t4) + TableQuantity(t5);
  {
      TableQuantityConcat4(t1, t2, t3, t4);
      TableQuantityConcat(t1 + t2 + t3 + t4, t5);
  }

//////////////////////////////////////////////////////////////////////////////
// shifting
//////////////////////////////////////////////////////////////////////////////

  predicate IsTableRightShift(table: FixedTable, table': FixedTable, inserted: Option<Entry>, start: Index, end: Index)
  {
    && (start <= end ==>
      && (forall i | 0 <= i < start :: table'[i] == table[i])
      && table'[start] == inserted
      && (forall i | start < i <= end :: table'[i] == table[i-1])
      && (forall i | end < i < |table'| :: table'[i] == table[i]))
    && (start > end ==>
      && table'[0] == table[ |table| - 1]
      && (forall i | 0 < i <= end :: table'[i] == table[i-1])
      && (forall i | end < i < start :: table'[i] == table[i])
      && table'[start] == inserted
      && (forall i | start < i < |table'| :: table'[i] == table[i-1]))
  }

  function TableRightShift(table: FixedTable, inserted: Option<Entry>, start: Index, end: Index) : (table': FixedTable)
    ensures IsTableRightShift(table, table', inserted, start, end)
  {
    if start <= end then
      table[..start] + [inserted] + table[start..end] + table[end+1..]
    else
      var last_index := |table| - 1;
      [table[last_index]] + table[..end] + table[end+1..start] + [inserted] + table[start..last_index]
  }
  
  lemma RightShiftIndex(table: FixedTable, table': FixedTable, inserted: Option<Entry>, start: Index, end: Index, i: Index)
    requires IsTableRightShift(table, table', inserted, start, end)
    ensures Partial(NextIndex(start), NextIndex(end)).Contains(i) ==> table'[i] == table[PrevIndex(i)];
    ensures Partial(NextIndex(end), start).Contains(i) ==> table'[i] == table[i];
    ensures i == start ==> table'[i] == inserted;
  {
  }

  lemma RightShiftPSL(table: FixedTable, table': FixedTable, inserted: Option<Entry>, start: Index, end: Index, i: Index)
    requires TableInv(table)
    requires IsTableRightShift(table, table', inserted, start, end)
    requires SlotFull(table'[i])
    requires Partial(NextIndex(start), NextIndex(end)).Contains(i)
    requires exists e : Index :: SlotEmpty(table[e])
    // requires i != hash(table[PrevIndex(i)].value.key)
    ensures SlotPSL(table', i) == SlotPSL(table, PrevIndex(i)) + 1
  {
    var old_i := PrevIndex(i);
    assert table'[i] == table[old_i];
    var h := hash(table[old_i].value.key);

    if i == h {
      var e : Index :| SlotEmpty(table[e]);
      assert ValidPSL(table, old_i);
      assert Partial(h, old_i).Contains(e);
      assert false;
    }
  }

  lemma RightShiftTableQuantity(table: FixedTable, table': FixedTable, inserted: Option<Entry>, start: Index, end: Index)
    requires IsTableRightShift(table, table', inserted, start, end)
    ensures TableQuantity(table') == TableQuantity(table) + EntryQuantity(inserted) - EntryQuantity(table[end]);
  {
    assert TableQuantity([table[end]]) == EntryQuantity(table[end])
      && TableQuantity([inserted]) == EntryQuantity(inserted) by {
        reveal TableQuantity();
    }

    if start <= end {
      assert table == table[..start] + table[start..end] + [table[end]] + table[end+1..];
      assert table' == table[..start] + [inserted] + table[start..end] + table[end+1..];
      TableQuantityConcat4(table[..start], table[start..end], [table[end]], table[end+1..]);
      TableQuantityConcat4(table[..start], [inserted], table[start..end], table[end+1..]);
    } else {
      var last_index := |table| - 1;
      assert table' == [table[last_index]] + table[..end] + table[end+1..start] + [inserted] + table[start..last_index];
      assert table == table[..end] + [table[end]] + table[end+1..start] + table[start..last_index] + [table[last_index]];
      TableQuantityConcat5([table[last_index]], table[..end], table[end+1..start], [inserted], table[start..last_index]);
      TableQuantityConcat5(table[..end], [table[end]], table[end+1..start], table[start..last_index], [table[last_index]]);
    }
  }

  predicate IsTableLeftShift(table: FixedTable, table': FixedTable, start: Index, end: Index)
  {
    && (start <= end ==>
      && (forall i | 0 <= i < start :: table'[i] == table[i]) 
      && (forall i | start <= i < end :: table'[i] == table[i+1]) 
      && table'[end] == Some(Empty)
      && (forall i | end < i < |table'| :: table'[i] == table[i]))
    && (start > end ==>
      && (forall i | 0 <= i < end :: table'[i] == table[i+1])
      && table'[end] == Some(Empty)
      && (forall i | end < i < start :: table'[i] == table[i])
      && (forall i | start <= i < |table'| - 1 :: table'[i] == table[i+1])
      && table'[ |table'| - 1 ] == table[0])
  }

  function TableLeftShift(table: FixedTable, start: Index, end: Index): (table': FixedTable)
    ensures IsTableLeftShift(table, table', start, end)
  {
    if start <= end then
      table[..start] + table[start+1..end+1] + [Some(Empty)] + table[end+1..]
    else
      table[1..end+1] + [Some(Empty)] + table[end+1..start] + table[start+1..] + [table[0]]
  }

  lemma LeftShiftIndex(table: FixedTable, table': FixedTable, start: Index, end: Index, i: Index)
    requires IsTableLeftShift(table, table', start, end)
    ensures Partial(start, end).Contains(i) ==> table'[i] == table[NextIndex(i)];
    ensures Partial(NextIndex(end), start).Contains(i) ==> table'[i] == table[i];
    ensures i == end ==> table'[i] == Some(Empty);
  {
  }

  lemma LeftShiftPSL(table: FixedTable, table': FixedTable, start: Index, end: Index, i: Index)
    requires TableInv(table)
    requires IsTableLeftShift(table, table', start, end)
    requires SlotFull(table'[i])
    requires Partial(start, end).Contains(i) 
    requires NextIndex(i) != hash(table[NextIndex(i)].value.key)
    ensures SlotPSL(table', i) == SlotPSL(table, NextIndex(i)) - 1
  {
    assert table'[i] == table[NextIndex(i)];
  }

  lemma LeftShiftTableQuantity(table: FixedTable, table': FixedTable, start: Index, end: Index)
    requires IsTableLeftShift(table, table', start, end)
    ensures TableQuantity(table') == TableQuantity(table) - EntryQuantity(table[start])
  {
    assert TableQuantity([Some(Empty)]) == 0
      && TableQuantity([table[start]]) == EntryQuantity(table[start]) by {
        reveal TableQuantity();
    }
    if start <= end {
      TableQuantityConcat4(table[..start], [table[start]], table[start+1..end+1], table[end+1..]);
      TableQuantityConcat4(table[..start], table[start+1..end+1], [Some(Empty)], table[end+1..]);
      assert table == table[..start] + [table[start]] + table[start+1..end+1] + table[end+1..];
      assert table' == table[..start] + table[start+1..end+1] + [Some(Empty)] + table[end+1..];
    } else {
      TableQuantityConcat5([table[0]], table[1..end+1], table[end+1..start], [table[start]], table[start+1..]);
      TableQuantityConcat5(table[1..end+1], [Some(Empty)], table[end+1..start], table[start+1..], [table[0]]);
      assert table == [table[0]] + table[1..end+1] + table[end+1..start] + [table[start]] + table[start+1..];
      assert table' == table[1..end+1] + [Some(Empty)] + table[end+1..start] + table[start+1..] + [table[0]];
    }
  }

//////////////////////////////////////////////////////////////////////////////
// refinements
//////////////////////////////////////////////////////////////////////////////

  function I(table: Table): map<Key, Value>
    requires TableWF(table)
  {
    if |table| == 0 then map[]
    else
      var item := Last(table).value;
      var rest := I(DropLast(table));
      if item.Empty? then rest else rest[item.key := item.value]
  }

  predicate SlotFullWithKey(entry: Option<Entry>, key: Key)
  {
    && SlotFull(entry)
    && entry.value.WithKey(key)
  }

  predicate TableContainsKey(table: Table, key: Key)
  {
    exists i: nat :: i < |table| && SlotFullWithKey(table[i], key)
  }

  function GetKeyIndex(table: Table, key: Key) : (i: nat)
    requires TableContainsKey(table, key)
    ensures i < |table|
    ensures SlotFullWithKey(table[i], key)
  {
    var i: nat :| i < |table| && SlotFullWithKey(table[i], key);
    i
  }

  function TableGetValue(table: Table, key: Key) : Value
    requires TableContainsKey(table, key)
  {
    var i := GetKeyIndex(table, key);
    table[i].value.value
  }

  lemma SubTableContainment(table: Table, key: Key)
    requires TableContainsKey(table, key)
    requires !SlotFullWithKey(Last(table), key)
    ensures TableContainsKey(DropLast(table), key)
  {
    assert |table| >= 2;
    var rest := DropLast(table);

    if |table| == 2 {
      assert SlotFullWithKey(rest[0], key);
      assert TableContainsKey(rest, key);
      return;
    }

    if SlotFullWithKey(Last(rest), key) {
      return;
    }

    if !TableContainsKey(rest, key) {
      assert forall i: nat ::
        i < |table| ==> !SlotFullWithKey(table[i], key);
      assert false;
    }
  }

  lemma ContainmentNecessary(table: Table, key: Key)
    requires TableWF(table)
    requires TableContainsKey(table, key)
    ensures key in I(table)
    ensures I(table)[key] == TableGetValue(table, key)
  {
    if SlotFullWithKey(Last(table), key) {
      return;
    }

    var rest := DropLast(table);

    if TableContainsKey(rest, key) {
      ContainmentNecessary(rest, key);
    } else {
      SubTableContainment(table, key);
    }
  }

  lemma ContainmentSufficient(table: Table, key: Key)
    requires TableWF(table)
    requires key in I(table)
    requires TableContainsKey(table, key)
    ensures I(table)[key] == TableGetValue(table, key)
  {
    if SlotFullWithKey(Last(table), key) {
      return;
    }

    var rest := DropLast(table);

    SubTableContainment(table, key);
    ContainmentSufficient(rest, key);
  }

  lemma ContainmentEquivalent(table: Table, key: Key)
    requires TableWF(table)
    ensures key in I(table) <==> TableContainsKey(table, key)
    ensures key in I(table) ==> I(table)[key] == TableGetValue(table, key)
  {
    if key in I(table) {
      ContainmentSufficient(table, key);
    }

    if TableContainsKey(table, key) {
      ContainmentNecessary(table, key);
    }
  }

  lemma RightShiftPreservesMapping(table: FixedTable, table': FixedTable, inserted: Entry)
    requires TableWF(table)
    requires TableWF(table')
    requires inserted.Full?
    requires !TableContainsKey(table, inserted.key)
    requires exists start: Index, end: Index
      :: IsTableRightShift(table, table', Some(inserted), start, end) && SlotEmpty(table[end])
    ensures I(table') == I(table)[inserted.key := inserted.value];
  {
    var m, m' := I(table), I(table');

    var start: Index, end: Index :|
      IsTableRightShift(table, table', Some(inserted), start, end) && SlotEmpty(table[end]);

    forall key : Key | key != inserted.key
      ensures (key in m <==> key in m')
      ensures (key in m ==> m[key] == m'[key])
    {
      if TableContainsKey(table, key) {
        var j := GetKeyIndex(table, key);
        var value := table[j].value.value;
        if table[j] == table'[j] {
          assert TableGetValue(table', key) == value;
        } else if table[j] == table'[NextIndex(j)] {
          assert TableGetValue(table', key) == value;
        } else {
          assert false;
        }
      }
      ContainmentEquivalent(table, key);
      ContainmentEquivalent(table', key);
    }

    assert inserted.key in m' && m'[inserted.key] == inserted.value by {
      assert SlotFullWithKey(table'[start], inserted.key);
      assert TableGetValue(table', inserted.key) == inserted.value;
      ContainmentEquivalent(table', inserted.key);
    }

    assert forall key : Key :: 
        && (key != inserted.key ==> (
          && (key in m <==> key in m')
          && (key in m ==> m[key] == m'[key])))
        && (key == inserted.key ==>
          m'[inserted.key] == inserted.value);
    
    assert m' == m[inserted.key := inserted.value];
  }

  lemma LeftShiftPreservesMapping(table: FixedTable, table': FixedTable, removed_key: Key)
    requires TableWF(table)
    requires TableWF(table')
    requires exists start: Index, end: Index
      :: IsTableLeftShift(table, table', start, end) && SlotFullWithKey(table[start], removed_key)
    ensures I(table') == I(table) - {removed_key}
  {
    var m, m' := I(table), I(table');

    forall key : Key | key != removed_key
      ensures (key in m <==> key in m')
      ensures (key in m ==> m[key] == m'[key])
    {
      if TableContainsKey(table, key) {
        var j := GetKeyIndex(table, key);
        var value := table[j].value.value;
        if table[j] == table'[j] {
          assert TableGetValue(table', key) == value;
        } else if table[j] == table'[PrevIndex(j)] {
          assert TableGetValue(table', key) == value;
        } else {
          assert false;
        }
      }
      ContainmentEquivalent(table, key);
      ContainmentEquivalent(table', key);
    }

    assert removed_key !in m' by {
      if TableContainsKey(table', removed_key) {
        var j : Index :| SlotFullWithKey(table'[j], removed_key);
        assert SlotFullWithKey(table[j], removed_key)
          || SlotFullWithKey(table[NextIndex(j)], removed_key);
        assert false; 
      }
      ContainmentEquivalent(table, removed_key);
      ContainmentEquivalent(table', removed_key);
    }

    assert forall key : Key :: 
        && (key != removed_key ==> (
          && (key in m <==> key in m')
          && (key in m ==> m[key] == m'[key])))
        && (key == removed_key ==>
          removed_key !in m');
    
    assert m' == m - {removed_key};
  }

  lemma OverwritePreservesMapping(table: FixedTable, table': FixedTable, end: Index, inserted: Entry)
    requires TableWF(table)
    requires TableWF(table')
    requires inserted.Full?
    requires SlotFullWithKey(table[end], inserted.key)
    requires table' == table[end := Some(inserted)]
    ensures I(table') == I(table)[inserted.key := inserted.value];
  {
    var m, m' := I(table), I(table');

    forall key : Key | key != inserted.key
      ensures (key in m <==> key in m')
      ensures (key in m ==> m[key] == m'[key])
    {
      if TableContainsKey(table, key) {
        var j := GetKeyIndex(table, key);
        var value := table[j].value.value;
        assert table[j] == table'[j]; 
        assert TableGetValue(table', key) == value;
      }
      ContainmentEquivalent(table, key);
      ContainmentEquivalent(table', key);
    }

    assert inserted.key in m' && m'[inserted.key] == inserted.value by {
      assert SlotFullWithKey(table'[end], inserted.key);
      assert TableGetValue(table', inserted.key) == inserted.value;
      ContainmentEquivalent(table', inserted.key);
    }

    assert forall key : Key :: 
        && (key != inserted.key ==> (
          && (key in m <==> key in m')
          && (key in m ==> m[key] == m'[key])))
        && (key == inserted.key ==>
          m'[inserted.key] == inserted.value);
    
    assert m' == m[inserted.key := inserted.value];
  }

//////////////////////////////////////////////////////////////////////////////
// unwrapping
//////////////////////////////////////////////////////////////////////////////

  function {:fuel 1} UnwrapRange(table: FixedTable, range: Range): (s: seq<Entry>)
    requires RangeKnown(table, range)
    ensures |range| == |s|
    decreases |range|
  {
    if range.HasNone() then
      assert |range| == 0;
      []
    else
      var last := range.GetLast();
      UnwrapRange(table, range.RightShrink1()) + [table[last].value]
  }

  lemma UnwrapRangeIndex(table: FixedTable, r1: Range, entries: seq<Entry>)
    requires r1.Partial?
    requires RangeKnown(table, r1) 
    requires UnwrapRange(table, r1) == entries
    ensures forall i: Index :: r1.Contains(i) ==>  
      table[i].value == entries[LeftShift(i, r1.start)]
    ensures forall j: Index :: 0 <= j < |entries| ==> 
      entries[j] == table[RightShift(r1.start, j)].value
    decreases |r1|
  {
    if r1.HasSome() {
      UnwrapRangeIndex(table, r1.RightShrink1(), DropLast(entries));
    }
  }

  // lemma UnwrapRangeSingleton(table: FixedTable, r1: Range, i: Index)
  //   requires r1.Partial?
  //   requires RangeKnown(table, r1) 
  //   requires r1.Contains(i)
  // {
  //   var entries := UnwrapRange(table, r1);
  //   UnwrapRangeIndex(table, r1, entries);
  //   assert UnwrapRange(table, Partial(i, NextIndex(i))) == [table[i].value];
  // }

  lemma UnwrapSplitRange(table: FixedTable, r1: Range, i: Index)
    requires r1.Partial?
    requires r1.Contains(i) || i == r1.end
    requires RangeKnown(table, r1)
    ensures UnwrapRange(table, r1) == 
        UnwrapRange(table, Partial(r1.start, i)) +
        UnwrapRange(table, Partial(i, r1.end))
    decreases if i == r1.end then 0 else 
      WrappedDistance(i, r1.end), |r1|
  {
    if |r1| == 1 {
      return;
    }

    if i == r1.end || i == r1.start {
      return;
    }

    var t := UnwrapRange(table, r1);
    var j := NextIndex(i);
    var tj1 := UnwrapRange(table, Partial(r1.start, j));
    var tj2 := UnwrapRange(table, Partial(j, r1.end));
    var ti1 := UnwrapRange(table, Partial(r1.start, i));
    var ti2 := UnwrapRange(table, Partial(i, r1.end));

    assert t == tj1 + tj2 by {
      UnwrapSplitRange(table, r1, j);
    }

    assert ti1 + [table[i].value] == tj1;

    assert ti2 == UnwrapRange(table, Partial(i, j)) + tj2 by {
      UnwrapSplitRange(table, Partial(i, r1.end), j);
    }

    assert UnwrapRange(table, Partial(i, j)) == [table[i].value];
    // UnwrapRangeSingleton(table, r1, i);
  }

  lemma UnwrapPrefixRange(table: FixedTable, r1: Range, r2: Range, entries: seq<Entry>)
    requires r1.Partial? && r2.Partial?
    requires r1.start == r2.start
    requires r1.Contains(r2.end)
    requires RangeKnown(table, r1) 
    requires UnwrapRange(table, r1) == entries
    ensures UnwrapRange(table, r2) == entries[ ..|r2| ]
    decreases |r2|
  {
    if |r2| == 0 {
      return;
    }

    var entries2 := UnwrapRange(table, r2);
    var last := r2.GetLast();
    var r3 := r2.RightShrink1();
    var l2, l3 := |r2|, |r3|;

    calc {
      UnwrapRange(table, r2);
      UnwrapRange(table, r3) + [table[last].value];
      {
        UnwrapPrefixRange(table, r1, r3, entries);
      }
      entries[..l3] + [table[last].value];
      {
        assert entries[l3] == table[last].value by {
          UnwrapRangeIndex(table, r1, entries);
          assert last == RightShift(r1.start, l3); 
        }
      }
      entries[..l3] + [entries[l3]];
      {
        assert entries[ ..l3] + [entries[l3]] == entries[..l2];
      }
      entries[..l2];
    }
  }

  lemma UnwrapSuffixRange(table: FixedTable, r1: Range, r2: Range, entries: seq<Entry>)
    requires r1.Partial? && r2.Partial?
    requires r1.end == r2.end
    requires r1.Contains(r2.start) || r2.start == r1.end
    requires RangeKnown(table, r1) 
    requires UnwrapRange(table, r1) == entries
    ensures UnwrapRange(table, r2) == entries[ |entries| - |r2| .. ]
  {
    if r2.start == r1.end {
      return;
    }

    var entries2 := UnwrapRange(table, r2);
    var split := r2.start;
    var r3 := Partial(r1.start, split);

    assert UnwrapRange(table, r1) == 
      UnwrapRange(table, r3) +
      UnwrapRange(table, r2) by {
      UnwrapSplitRange(table, r1, split);
    }

    assert UnwrapRange(table, r3) == entries[ ..|r3| ] by {
      UnwrapPrefixRange(table, r1, r3, entries);
    }

    assert UnwrapRange(table, r2) == entries[ |entries| - |r2| .. ];
  }

  lemma UnwrapSubRange(table: FixedTable, r1: Range, r2: Range, entries: seq<Entry>)
    requires r1.Partial? && r2.Partial?
    requires r1.Contains(r2.start)
    requires r1.Contains(r2.end) || r2.end == r1.end
    requires Partial(r1.start, r2.end).Contains(r2.start) || r2.start == r2.end

    requires RangeKnown(table, r1) 
    requires UnwrapRange(table, r1) == entries
    ensures UnwrapRange(table, r2) ==
      entries[WrappedDistance(r1.start, r2.start) ..
        |entries| - WrappedDistance(r2.end, r1.end)];
  {
    var Partial(s1, e1) := r1;
    var Partial(s2, e2) := r2;

    var t2 := UnwrapRange(table, Partial(s1, s2));
    var t3 := UnwrapRange(table, r2);
    var t4 := UnwrapRange(table, Partial(e2, e1));

    assert entries == t2 + t3 + t4 by {
      UnwrapSplitRange(table, Partial(s1, e2), s2);
      UnwrapSplitRange(table, r1, e2);
    }

    assert t2 == entries[..|t2| ] by {
      UnwrapPrefixRange(table, r1, Partial(s1, s2), entries);
    }

    assert t4 == entries[ |entries| - |t4| .. ] by {
      UnwrapSuffixRange(table, r1, Partial(e2, e1), entries);
    }

    assert t3 == entries[ |t2| .. |entries| - |t4| ];

    assert |t2| == WrappedDistance(r1.start, r2.start);
    assert |t4| == WrappedDistance(r2.end, r1.end);
  }

  lemma RangeEquivalentUnwrap(t1: FixedTable, t2: FixedTable, range: Range)
    requires RangeEquivalent(t1, t2, range)
    requires forall i: Index :: range.Contains(i) ==> t1[i].Some?
    ensures UnwrapRange(t1, range) == UnwrapRange(t2, range)
    decreases |range|
  {
    if range.HasSome() {
      var last := range.GetLast();
      assert t1[last] == t2[last];
      var range' := range.RightShrink1();
      RangeEquivalentUnwrap(t1, t2, range');
    } 
  }

  predicate RangeRightShift1Equivalent(t1: FixedTable, t2: FixedTable, r: Range)
  {
    forall i: Index :: r.Contains(i) ==> t1[i] == t2[NextIndex(i)]
  }

  lemma RangeShiftEquivalentUnwrap(t1: FixedTable, t2: FixedTable, r1: Range)
    requires r1.Partial?
    requires RangeRightShift1Equivalent(t1, t2, r1)
    requires forall i: Index :: r1.Contains(i) ==> t1[i].Some?
    ensures forall i: Index :: r1.RightShift1().Contains(i) ==> t2[i].Some?
    ensures UnwrapRange(t1, r1) == UnwrapRange(t2, r1.RightShift1())
    decreases |r1|
  {
    var r2 := r1.RightShift1();
    if r1.HasSome() {
      forall i: Index | r2.Contains(i)
        ensures t2[i] == t1[PrevIndex(i)]
      {
        assert r1.Contains(PrevIndex(i));
      }

      var last := r1.GetLast();
      assert t1[last] == t2[NextIndex(last)];
      var r1' := r1.RightShrink1();
      RangeShiftEquivalentUnwrap(t1, t2, r1');
    }
  }

  lemma RightShiftUnwrap(t1: FixedTable, t2: FixedTable,
    inserted: Entry, entries: seq<Entry>,
    range: Range, start: Index)
    requires range.Partial?
    requires range.Contains(start)
    requires RangeKnown(t1, range)
    requires UnwrapRange(t1, range) == entries
    requires IsTableRightShift(t1, t2, Some(inserted), start, PrevIndex(range.end))
    ensures var probe_len := WrappedDistance(range.start, start);
      UnwrapRange(t2, range) == entries[..probe_len] + [inserted] + entries[probe_len..|entries| - 1];
  {
    var end := PrevIndex(range.end);
    var probe_range := Partial(range.start, start);
    var shift_range := Partial(start, end);
    var probe_len := |probe_range|;
    var len := |range|;

    assert UnwrapRange(t1, range) == entries;

    assert UnwrapRange(t2, probe_range) == entries[..probe_len] by {
      assert RangeEquivalent(t1, t2, probe_range);
      RangeEquivalentUnwrap(t1, t2, probe_range);
      UnwrapPrefixRange(t1, range, probe_range, entries);
      // assert UnwrapRange(t1, probe_range) == UnwrapRange(t2, probe_range);
    }

    assert UnwrapRange(t2, shift_range.RightShift1()) == entries[probe_len..len - 1] by {
      RangeShiftEquivalentUnwrap(t1, t2, shift_range);
      UnwrapSubRange(t1, range, shift_range, entries);
      // assert UnwrapRange(t1, shift_range) == UnwrapRange(t2, shift_range.RightShift1());
    }

    var start_next := NextIndex(start);
    
    assert UnwrapRange(t2, range) == UnwrapRange(t2, probe_range)
      + UnwrapRange(t2, Partial(start, start_next))
      + UnwrapRange(t2, shift_range.RightShift1()) by {
      UnwrapSplitRange(t2, range, start_next);
      UnwrapSplitRange(t2, Partial(range.start, start_next), start);
    }

    assert UnwrapRange(t2, Partial(start, start_next)) == [inserted] by {
      assert t2[start] == Some(inserted);
    }

    assert UnwrapRange(t2, range) == entries[..probe_len] + [inserted] + entries[probe_len..len - 1];
  }

  // lemma OverwriteUnwrap(t1: FixedTable, t2: FixedTable,
  //   inserted: Entry, entries: seq<Entry>,
  //   range: Range, start: Index)
  //   requires range.Partial?
  //   requires range.Contains(start)
  //   requires RangeKnown(t1, range)
  //   requires UnwrapRange(t1, range) == entries
  //   requires t2 == t1[start := Some(inserted)]
  // {
  //   var probe_range := Partial(range.start, start);
  //   var probe_len := |probe_range|;

  //   assert UnwrapRange(t2, probe_range) == entries[..probe_len] by {
  //     assert RangeEquivalent(t1, t2, probe_range);
  //     RangeEquivalentUnwrap(t1, t2, probe_range);
  //     UnwrapPrefixRange(t1, range, probe_range, entries);
  //   }
  // }

}
  // lemma ValidHashSegmentsImpliesDisjoint(table: FixedTable, h0: Index, h1: Index)
  //   requires h0 != h1
  //   requires Complete(table)
  //   requires ValidHashSegments(table)
  //   ensures !GetHashSegment(table, h0).OverlapsWith(GetHashSegment(table, h1))
  // {
  //   var range0 := GetHashSegment(table, h0);
  //   var range1 := GetHashSegment(table, h1);

  //   forall i : Index | range0.Contains(i)
  //     ensures !range1.Contains(i)
  //   {
  //     assert table[i].value.Full?;
  //     assert SlotKeyHash(table, i) == h0;
  //     assert SlotKeyHash(table, i) != h1;
  //   }

  //   forall i : Index | range1.Contains(i)
  //     ensures !range0.Contains(i)
  //   {
  //     assert table[i].value.Full?;
  //     assert SlotKeyHash(table, i) == h1;
  //     assert SlotKeyHash(table, i) != h0;
  //   }
  // }

  // predicate ValidOrdering(table: FixedTable, h0: Index)
  // requires Complete(table)
  // requires ValidHashSegments(table)
  // {
  //   var h1 := NextIndex(h0);
  //   var range0 := GetHashSegment(table, h0);
  //   var range1 := GetHashSegment(table, h1);
  //   // this part should all be empty (we won't have a none-empty segment in between)
  //   (forall i : Index | Contains(GetBetween(range0, range1), i) :: table[i].value.Empty?)
  // }
