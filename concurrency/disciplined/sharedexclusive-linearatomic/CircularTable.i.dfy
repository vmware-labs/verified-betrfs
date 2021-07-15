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

//////////////////////////////////////////////////////////////////////////////
// entry/range predicates
//////////////////////////////////////////////////////////////////////////////

  // PSL == Probe Sequence Length: the probe length from hash(key)
  // to index i
  function PSL(key: Key, i: Index): nat
  {
    var h := hash(key);
    if h <= i then
      i - h
    else
      FixedSize() - h + i
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
    hash(entry.value.key)
  }

  // What's the Probe Sequence Length for the key at this location?
  function SlotPSL(table: FixedTable, i: Index): nat
    requires SlotFull(table[i])
  {
    PSL(table[i].value.key, i)
  }

  predicate SlotEmpty(entry: Option<Entry>)
  {
    entry.Some? && entry.value.Empty?
  }

  predicate SlotFullWithOtherKey(entry: Option<Entry>, key: Key)
  {
    && SlotFull(entry)
    && entry.value.key != key
  }

  predicate RangeFullWithOtherKeys(table: FixedTable, range: Range, key: Key)
  {
    forall i: Index | range.Contains(i) :: SlotFullWithOtherKey(table[i], key)
  }

  predicate SlotShouldSkip(entry: Option<Entry>, i: Index, key: Key)
  {
    && SlotFullWithOtherKey(entry, key)
    // the psl at the slot is geq than the psl of insert
    && PSL(entry.value.key, i) >= PSL(key, i)
  }

  predicate SlotShouldSwap(entry: Option<Entry>, i: Index, key: Key)
  {
    && SlotFullWithOtherKey(entry, key)
    // the psl at the slot is less than the psl of the insert
    && PSL(entry.value.key, i) < PSL(key, i)
  }

  predicate SlotShouldTidy(entry: Option<Entry>, i: Index)
  {
    && SlotFull(entry)
    && hash(entry.value.key) != i
  }

  predicate ValidTidyRange(table: FixedTable, r: Range, key: Key)
  {
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
    ensures
      var end_next := NextIndex(r.end);
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

  predicate ValidProbeRange(table: FixedTable, key: Key, end: Index)
  {
    // skip upto (not including) start
    && (forall i: Index | Partial(hash(key), end).Contains(i) :: SlotShouldSkip(table[i], i, key))
    // insert at start
    && (SlotShouldSwap(table[end], end, key)
      || SlotEmpty(table[end]))
  }

  // a valid probe range would cover key's hash segment 
  lemma ProbeRangeSufficient(table: FixedTable, key: Key, end: Index)
    requires TableInv(table)
    requires ValidProbeRange(table, key, end)
    ensures var h_range := GetHashSegment(table, hash(key));
      h_range.HasSome() ==> (
        && Partial(hash(key), end).Contains(h_range.start)
        && end == h_range.end
      )
    ensures !(exists i: Index ::
      SlotFull(table[i]) && table[i].value.key == key)
  {
    var h := hash(key);
    var p_range := Partial(h, end);

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
    && entry.value.key == key
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

  lemma RightShiftPreservesContainment(table: FixedTable, table': FixedTable, inserted: Entry)
    requires TableWF(table)
    requires TableWF(table')
    requires inserted.Full?
    requires !TableContainsKey(table, inserted.key)
    requires exists start: Index, end: Index
      :: IsTableRightShift(table, table', Some(inserted), start, end) && SlotEmpty(table[end])
   ensures forall key : Key | key != inserted.key :: 
      && (TableContainsKey(table, key) <==> TableContainsKey(table', key))
      && (TableContainsKey(table, key) ==> TableGetValue(table, key) == TableGetValue(table', key)) 
    ensures TableContainsKey(table', inserted.key)
    ensures TableGetValue(table', inserted.key) == inserted.value
  {
    var start: Index, end: Index :|
      IsTableRightShift(table, table', Some(inserted), start, end) && SlotEmpty(table[end]);

    forall key : Key | key != inserted.key
      ensures TableContainsKey(table, key) <==> TableContainsKey(table', key)
      ensures TableContainsKey(table, key) ==> TableGetValue(table, key) == TableGetValue(table', key)
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
    }

    assert SlotFullWithKey(table'[start], inserted.key);
    assert TableGetValue(table', inserted.key) == inserted.value;
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

    RightShiftPreservesContainment(table, table', inserted);
    forall key : Key | key != inserted.key
      ensures 
          && (key in m <==> key in m')
          && (key in m ==> m[key] == m'[key])
    {
      ContainmentEquivalent(table, key);
      ContainmentEquivalent(table', key);
    }

    assert inserted.key in m' && m'[inserted.key] == inserted.value by {
      ContainmentEquivalent(table, inserted.key);
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

  lemma LeftShiftPreservesContainment(table: FixedTable, table': FixedTable, removed_key: Key)
    requires TableWF(table)
    requires TableWF(table')
    requires exists start: Index, end: Index
      :: IsTableLeftShift(table, table', start, end) && SlotFullWithKey(table[start], removed_key)
    ensures forall key : Key | key != removed_key ::
      && (TableContainsKey(table, key) <==> TableContainsKey(table', key))
      && (TableContainsKey(table, key) ==> TableGetValue(table, key) == TableGetValue(table', key)) 
    ensures !TableContainsKey(table', removed_key)
  {
    var start: Index, end: Index :|
      IsTableLeftShift(table, table', start, end) && SlotFullWithKey(table[start], removed_key);

    forall key : Key | key != removed_key
      ensures TableContainsKey(table, key) <==> TableContainsKey(table', key)
      ensures TableContainsKey(table, key) ==> TableGetValue(table, key) == TableGetValue(table', key)
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
    }
    if TableContainsKey(table', removed_key) {
      var j : Index :| SlotFullWithKey(table'[j], removed_key);
      assert SlotFullWithKey(table[j], removed_key)
        || SlotFullWithKey(table[NextIndex(j)], removed_key);
      assert false; 
    }
  }

  lemma LeftShiftPreservesMapping(table: FixedTable, table': FixedTable, removed_key: Key)
    requires TableWF(table)
    requires TableWF(table')
    requires exists start: Index, end: Index
      :: IsTableLeftShift(table, table', start, end) && SlotFullWithKey(table[start], removed_key)
    ensures I(table') == I(table) - {removed_key}
  {
    var m, m' := I(table), I(table');

    LeftShiftPreservesContainment(table, table', removed_key);

    forall key : Key | key != removed_key
      ensures 
        && (key in m <==> key in m')
        && (key in m ==> m[key] == m'[key])
    {
      ContainmentEquivalent(table, key);
      ContainmentEquivalent(table', key);
    }

    assert removed_key !in m' by {
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
//    assert table'[i] == table[PrevIndex(i)];
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
