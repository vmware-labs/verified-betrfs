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

  // This is the thing that's stored in the hash table at this row.
  datatype Entry =
    | Full(key: Key, value: Value)
    | Empty

  type Table = seq<Option<Entry>>

  type FixedTable = t: Table
    | |t| == FixedSize() witness *
    
  predicate Complete(table: FixedTable)
  {
    forall i: Index :: table[i].Some?
  }

  function UnitTable(): Table
  {
    seq(FixedSize(), i => None)
  }

//////////////////////////////////////////////////////////////////////////////
// robinhood invarints
//////////////////////////////////////////////////////////////////////////////

  // Keys are unique, although we don't count entries being removed
  predicate KeysUnique(table: FixedTable)
    requires Complete(table)
  {
    forall i: Index, j: Index | 
        && i != j
        && table[i].value.Full?
        && table[j].value.Full?
      :: table[i].value.key != table[j].value.key
  }

  predicate ValidHashSegment(table: FixedTable, hash: Index, range: Range)
    requires Complete(table)
  {
    // the segement can only be Partial
    && range.Partial?
    // // if the segment is Partial, the hash cannot be in the middle 
    // && (range.Partial? ==>
    //   !Contains(Partial(NextIndex(range.start), range.end), hash))
    // all the keys in the segment share the hash
    && (forall i: Index | range.Contains(i) ::
        && table[i].value.Full?
        && SlotKeyHash(table, i) == hash)
    // and no where else
    && (forall i: Index | !range.Contains(i) ::
        (table[i].value.Full? ==> 
        SlotKeyHash(table, i) != hash))
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

  predicate TableInv(table: FixedTable)
  {
    && Complete(table)
    && KeysUnique(table)
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

//////////////////////////////////////////////////////////////////////////////
// entry predicates
//////////////////////////////////////////////////////////////////////////////

  function PSL(key: Key, i: Index): nat
  {
    var h := hash(key);
    if h <= i then
      i - h
    else
      FixedSize() - h + i
  }

  function SlotKeyHash(table: FixedTable, i: Index): Index
    requires table[i].Some? && table[i].value.Full?
  {
    hash(table[i].value.key)
  }

  function SlotPSL(table: FixedTable, i: Index): nat
    requires table[i].Some? && table[i].value.Full?
  {
    PSL(table[i].value.key, i)
  }

  type EntryPredicate = (Option<Entry>, Index, Key) -> bool

  predicate TrueInRange(table: FixedTable, range: Range, key: Key, p: EntryPredicate)
  {
    forall i: Index | range.Contains(i) :: p(table[i], i, key)
  }

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

  lemma RightShiftedPSL(table: FixedTable, table': FixedTable, inserted: Option<Entry>, start: Index, end: Index, i: Index)
    requires IsTableRightShift(table, table', inserted, start, end)
    requires table'[i].Some? && table'[i].value.Full?
    requires Partial(NextIndex(start), NextIndex(end)).Contains(i)
    requires i != hash(table[PrevIndex(i)].value.key)
    ensures SlotPSL(table', i) == SlotPSL(table, PrevIndex(i)) + 1
  {
    assert table'[i] == table[PrevIndex(i)];
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
}