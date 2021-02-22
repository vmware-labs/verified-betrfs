include "MapSpec.s.dfy"
include "../../lib/Base/Option.s.dfy"

module RobinHood {
  import opened KeyValueType
  import opened NativeTypes
  import opened Options

  function method hash(key: uint64) : (h : uint32)

  datatype Entry =
    | Full(key: Key, value: Value)
    | Empty

  predicate KeysUnique(table: seq<Entry>)
  {
    forall i, j | 0 <= i < |table| && 0 <= j < |table|
        && i != j && table[i].Full? && table[j].Full?
        :: table[i].key != table[j].key
  }

  /*predicate ValidHashEntry(table: seq<Entry>, i: int, j: int)
  requires 0 <= i < |table|
  requires 0 <= j < |table|
  {
    table[i].Empty? && table[j].Full? ==> (
      var h := hash(table[j].key)
      // we need h to be between i and j, but cyclically
      && (i < j ==> i < h <= j)
      && (i > j ==> i < h || h <= j)
    )
  }*/

  /*predicate ValidHashNeighbors(table: seq<Entry>, i: int, j: int)
  requires 0 <= i < |table|
  requires 0 <= j < |table|
  {
    var k := (if j+1 < |table| then j+1 else 0);
    table[i].Empty? && table[j].Full? && table[j+1].Full? ==> (
      var h := hash(table[j].key)
      // we need h to be between i and j, but cyclically
      && (i < j ==> i < h <= j)
      && (i > j ==> i < h || h <= j)
    )
  }*/

  predicate ContiguousToEntry(table: seq<Entry>, i: int)
  requires 0 <= i < |table|
  {
    table[i].Full? ==> (
      var h := hash(table[i].key) as int;
      && (h <= i ==> (forall j | h <= j <= i :: table[j].Full?))
      && (h > i ==>
        && h < |table|
        && (forall j | 0 <= j <= i :: table[j].Full?)
        && (forall j | h <= j < |table| :: table[j].Full?)
      )
    )
  }

  // 'Robin Hood' order
  // It's not enough to say that hash(entry[i]) <= hash(entry[i+1])
  // because of wraparound. We do a cyclic comparison 'rooted' at an
  // arbitrary empty element, given by e.
  predicate ValidHashNeighbors(table: seq<Entry>, e: int, j: int)
  requires 0 <= e < |table|
  requires 0 <= j < |table|
  {
    var k := (if j+1 < |table| then j+1 else 0);
    (table[e].Empty? && table[j].Full? && table[k].Full? ==> (
      var hj := hash(table[j].key) as int;
      var hk := hash(table[k].key) as int;
      (e < hj <= hk || hj <= hk < e || hk < e < hj)
    ))
  }

  predicate ExistsEmptyEntry(table: seq<Entry>)
  {
    exists i :: 0 <= i < |table| && table[i].Empty?
  }

  predicate Inv(table: seq<Entry>)
  {
    && KeysUnique(table)
    && ExistsEmptyEntry(table)
    && (forall e, j | 0 <= e < |table| && 0 <= j < |table|
        :: ValidHashNeighbors(table, e, j))
    && (forall i | 0 <= i < |table|
        :: ContiguousToEntry(table, i))
  }

  // Ops

  // Map interpretation, queries

  function GetIndex(table: seq<Entry>, key: Key) : Option<int>
  {
    if i :| 0 <= i < |table| && table[i].Full? && table[i].key == key then (
      Some(i)
    ) else (
      None
    )
  }

  function GetValue(table: seq<Entry>, key: Key) : Option<Value>
  {
    var i := GetIndex(table, key);
    if i.Some? then Some(table[i.value].value) else None
  }

  lemma GetValue_for_found(table: seq<Entry>, i: int)
  requires Inv(table)
  requires 0 < i < |table|
  requires table[i].Full?
  ensures GetValue(table, table[i].key) == Some(table[i].value)
  {
  }

  predicate NotFoundInRange(table: seq<Entry>, key: Key, i: int)
  {
    var h := hash(key) as int;
    && 0 < i < |table|
    && table[i].Empty? // TODO could also use a comparison condition on the hash value
    && (h <= i ==> (forall j | h <= j < i :: table[j].Full? && table[j].key != key))
    && (h > i ==> (forall j | 0 <= j < i :: table[j].Full? && table[j].key != key))
    && (h > i ==> (forall j | h <= j < |table| :: table[j].Full? && table[j].key != key))
  }

  lemma GetValue_for_not_found(table: seq<Entry>, key: Key, i: int)
  requires Inv(table)
  requires NotFoundInRange(table, key,i)
  ensures GetValue(table, key) == None
  {
    forall j | 0 <= j < |table| && table[j].Full? && table[j].key == key
    ensures false
    {
      assert ContiguousToEntry(table, j);
      /*var h := hash(key) as int;
      if h <= j {
        if j < i {
          assert false;
        } else {
          assert false;
        }
      } else {
        assert false;
      }*/
    }
  }

  // Update existing key

  predicate Update(table: seq<Entry>, table': seq<Entry>, i: int, key: Key, value: Value)
  {
    && 0 <= i < |table|
    && table[i].Full?
    && table[i].key == key
    && table' == table[i := Full(key, value)]
  }

  lemma Update_Inv(table: seq<Entry>, table': seq<Entry>, i: int, key: Key, value: Value)
  requires Inv(table)
  requires Update(table, table', i, key, value)
  ensures Inv(table')
  {
    var i :| 0 <= i < |table| && table[i].Empty?;
    assert table'[i].Empty?;

    forall e, j | 0 <= e < |table'| && 0 <= j < |table'|
    ensures ValidHashNeighbors(table', e, j)
    {
      assert ValidHashNeighbors(table, e, j);
    }

    forall i | 0 <= i < |table'|
    ensures ContiguousToEntry(table', i)
    {
      assert ContiguousToEntry(table, i);
    }
  }

  lemma GetValue_Update_self(
      table: seq<Entry>, table': seq<Entry>,
      i: int, key: Key, value: Value)
  requires Inv(table)
  requires Update(table, table', i, key, value)
  ensures GetValue(table', key) == Some(value)
  {
    assert table'[i].key == key; // observe
    //assert GetIndex(table', key) == Some(i);
  }

  lemma GetValue_Update_other(
      table: seq<Entry>, table': seq<Entry>,
      i: int, key: Key, value: Value, other: Key)
  requires Inv(table)
  requires Update(table, table', i, key, value)
  requires other != key
  ensures GetValue(table', other) == GetValue(table, other)
  {
    if GetIndex(table, other).Some? {
      var j := GetIndex(table, other).value;
      assert table'[j].key == other;
      //assert GetIndex(table', other) == Some(j);
      //assert GetIndex(table, other) == GetIndex(table', other);
      //assert j != i;
    } else if GetIndex(table', other).Some? {
      //assert GetIndex(table, other) == GetIndex(table', other);
    } else {
      //assert GetIndex(table, other) == GetIndex(table', other);
    }
  }

  // Remove a key

  // delete a, then shift a+1,...,b to the left
  datatype LeftShift = LeftShift(start: int, end: int)

  predicate ApplyLeftShift(table: seq<Entry>, table': seq<Entry>, shift: LeftShift)
  {
    && 0 <= shift.start < |table|
    && 0 <= shift.end < |table|
    && |table'| == |table|

    && (shift.start <= shift.end ==>
      && (forall i | 0 <= i < shift.start :: table'[i] == table[i])
      && (forall i | shift.start <= i < shift.end :: table'[i] == table[i+1])
      && table'[shift.end] == Empty
      && (forall i | shift.end < i < |table'| :: table'[i] == table[i])
    )

    && (shift.start > shift.end ==>
      && (forall i | 0 <= i < shift.end :: table'[i] == table[i+1])
      && table'[shift.end] == Empty
      && (forall i | shift.end < i < shift.start :: table'[i] == table[i])
      && (forall i | shift.start <= i < |table'| - 1 :: table'[i] == table[i+1])
      && table'[|table'| - 1] == table[0]
    )
  }

  predicate Remove(table: seq<Entry>, table': seq<Entry>, key: Key, shift: LeftShift)
  {
    && 0 <= shift.start < |table|
    && 0 <= shift.end < |table|
    && table[shift.start].Full?
    && table[shift.start].key == key

    // The next element after 'end' should be the first element which is either
    // (i) empty or (ii) has hash value equal to its slot index
    && var next := (if shift.end == |table| - 1 then 0 else shift.end + 1);
    && (table[next].Full? ==> hash(table[next].key) as int == next)
    && (shift.start <= shift.end ==> forall j | shift.start < j <= shift.end
            :: table[j].Full? && hash(table[j].key) as int != j)
    && (shift.end < shift.start ==> forall j | (shift.start < j < |table| || 0 <= j <= shift.end)
            :: table[j].Full? && hash(table[j].key) as int != j)

    && ApplyLeftShift(table, table', shift)
  }

  predicate AllBetweenAreFull(table: seq<Entry>, a: int, b: int)
  {
    && 0 <= a < |table|
    && 0 <= b < |table|
    && (a < b ==> forall k | a < k < b :: table[k].Full?)
    && (a > b ==> forall k | 0 <= k < b :: table[k].Full?)
    && (a > b ==> forall k | a < k < |table| :: table[k].Full?)
  }

  lemma get_empty_slot_backwards(table: seq<Entry>, i: int)
  returns (j: int)
  requires 0 <= i < |table|
  requires ExistsEmptyEntry(table)
  ensures 0 <= j < |table|
  ensures table[j].Empty?
  ensures AllBetweenAreFull(table, j, i)
  {
    if table[i].Empty? {
      j := i;
      return;
    }

    j := i;
    while table[j].Full?
    invariant 0 <= j < |table|
    invariant AllBetweenAreFull(table, j, i)
    decreases |table| - (if j <= i then i - j else i - j + |table|)
    {
      if j == i+1 {
        assert false;
      }
      j := if j == 0 then |table| - 1 else j - 1;
    }
  }

  lemma get_empty_slot_forwards(table: seq<Entry>, i: int)
  returns (j: int)
  requires 0 <= i < |table|
  requires ExistsEmptyEntry(table)
  ensures 0 <= j < |table|
  ensures table[j].Empty?
  ensures AllBetweenAreFull(table, i, j)
  {
    if table[i].Empty? {
      j := i;
      return;
    }

    j := i;
    while table[j].Full?
    invariant 0 <= j < |table|
    invariant AllBetweenAreFull(table, i, j)
    decreases |table| - (if i <= j then j - i else j - i + |table|)
    {
      if j == i-1 {
        assert false;
      }
      j := if j == |table| - 1 then 0 else j + 1;
    }
  }

  lemma hash_neighbor_transitive(table: seq<Entry>, e: int, i: int, j: int)
  requires 0 <= e < |table|
  requires 0 <= i < |table|
  requires 0 <= j < |table|
  requires table[e].Empty?
  requires table[i].Full?
  requires table[j].Full?
  requires AllBetweenAreFull(table, i, j)
  requires (forall j | 0 <= j < |table|
        :: ValidHashNeighbors(table, e, j))
  requires (forall i | 0 <= i < |table|
        :: ContiguousToEntry(table, i))
  ensures 
      var hi := hash(table[i].key) as int;
      var hj := hash(table[j].key) as int;
      e < hi <= hj || hi <= hj < e || hj < e < hi

  decreases if j >= i then j - i else j - i + |table|
  {
    if i == j {
      assert ContiguousToEntry(table, i);
      return;
    }

    assert ValidHashNeighbors(table, e, i);

    var ip := (if i < |table| - 1 then i + 1 else 0);
    if ip == j {
      var hi := hash(table[i].key) as int;
      var hj := hash(table[j].key) as int;
      assert e != hi;
      assert e != hj;
    } else {
      hash_neighbor_transitive(table, e, ip, j);
    }
  }

  lemma Remove_Inv(table: seq<Entry>, table': seq<Entry>, key: Key, shift: LeftShift)
  requires Inv(table)
  requires Remove(table, table', key, shift)
  ensures Inv(table')
  {
    forall e, j | 0 <= e < |table| && 0 <= j < |table|
    ensures ValidHashNeighbors(table', e, j)
    {
      /*var e1 :| 0 <= e1 < |table| && table[e1].Empty?;
      assert table'[e1].Empty?;

      assert ValidHashNeighbors(table', e1, j);
      assert ValidHashNeighbors(table', e, j);*/

      /*assert ValidHashNeighbors(table, e, j);
      if e == shift.end {
        assert ValidHashNeighbors(table', e, j);
      } else {
        assert ValidHashNeighbors(table', e, j);
      }*/

      if e == shift.end {
        if table'[j].Full? {
          // suppose X is removed and bbbb is shifted:
          //
          // _aaaaXbbbbcccc_
          // _aaaabbbb_cccc_
          //
          // e1       e    e2
          //
          // There are four cases for j ... it could be the aaaa, bbbb, cccc, or
          // somewhere else. 
          // 
          // First we find e1 or e2, then determine where j is w.r.t. e1, e, e2

          var e1 := get_empty_slot_backwards(table, e);
          var e2 := get_empty_slot_forwards(table, e);
          var e_next := (if e < |table| - 1 then e + 1 else 0);

          //assert !table[e1].Full?;
          //assert table[shift.start].Full?;
          //assert e1 < shift.start <= e
          //    || e < e1 < shift.start
          //    || shift.start <= e < e1;
          assert e1 < e < e2
              || e < e2 <= e1
              || e2 <= e1 < e;

          if (e < j < e2) || (j < e2 < e) || (e2 < e < j) {
            // the cccc's case
            // we have hash(j) <= hash(j+1) w.r.t. position e1
            assert ValidHashNeighbors(table, e1, j);
            // we need to get the same w.r.t. position e
            // so we get e < e + 1 <= e_next == hash(e_next) <= hash(j) w.r.t. e1

            //assert table[j].key == table'[j].key;
            //assert hash(table[j].key) == hash(table'[j].key);
            hash_neighbor_transitive(table, e1, e_next, j);
            //assert e1 < e < hash(table[j].key) as int
            //    || e < hash(table[j].key) as int < e1
            //    || hash(table[j].key) as int < e1 < e;
            assert ValidHashNeighbors(table', e, j);
          } else if (e1 < j < e) || (j < e < e1) || (e < e1 < j) {
            var k := (if j < |table| - 1 then j + 1 else 0);
            var l := (if k < |table| - 1 then k + 1 else 0);

            //assert ValidHashNeighbors(table, e1, j);
            //hash_neighbor_transitive(table, e1, j, e);
            //assert ValidHashNeighbors(table, e1, k);
            //hash_neighbor_transitive(table, e1, k, e);
            //assert ValidHashNeighbors(table, e, j);
            //assert ValidHashNeighbors(table, e, k);
            //assert ValidHashNeighbors(table, e2, j);
            //assert ValidHashNeighbors(table, e2, k);
            //assert ContiguousToEntry(table, j);
            assert ContiguousToEntry(table, k);
            //assert ValidHashNeighbors(table, e2, j);
            //hash_neighbor_transitive(table, e2, j, e);
            //assert ValidHashNeighbors(table, e2, k);
            //hash_neighbor_transitive(table, e2, k, e);
            //assert ValidHashNeighbors(table, e1, k);

            // aaaa or bbbb case
            // we have hash(j) <= hash(j+1) w.r.t. position e1
            assert ValidHashNeighbors(table, e1, j);

            assert ValidHashNeighbors(table, e1, k);
            hash_neighbor_transitive(table, e1, k, e);

            assert ValidHashNeighbors(table, e1, l);
            if table[k].Full? && table[l].Full? && l != e && k != e {
              hash_neighbor_transitive(table, e1, l, e);
            }
            // we need to get the same w.r.t. position e
            // therefore we want
            // hash(j+1) <= e     w.r.t. position e1

            assert ContiguousToEntry(table, e);

            assert ValidHashNeighbors(table', e, j);
          } else {
            assert ValidHashNeighbors(table, e1, j);
            assert ValidHashNeighbors(table, e2, j);

            //assert ValidHashNeighbors(table', e1, j);
            //assert ValidHashNeighbors(table', e2, j);

            //assert e2 < j < e1 || j < e1 <= e2 || e1 <= e2 < j;

            /*var k := (if j+1 < |table| then j+1 else 0);
            if table[j].Full? && table[k].Full? {
              assert table[j] == table'[j];
              assert table[k] == table'[k];

              var hj := hash(table[j].key) as int;
              var hk := hash(table[k].key) as int;

              assert (e1 < hk ==> e1 < hj <= hk);
              assert (e1 > hk ==> e1 < hj || hj <= hk);

              assert (e2 < hk ==> e2 < hj <= hk);
              assert (e2 > hk ==> e2 < hj || hj <= hk);

              assert ContiguousToEntry(table, j);

              assert (e < hk ==> e < hj <= hk);
              assert (e > hk ==> e < hj || hj <= hk);
            }*/

            assert ContiguousToEntry(table, j);

            assert ValidHashNeighbors(table', e, j);
          }
        }

        assert ValidHashNeighbors(table', e, j);
      } else {
        // These 3 should handle all the cases. We need j+1 for the case
        // that slot j+1 shifted left to slot j. And of course we need 0
        // for the wraparound shift case. We'll let Dafny bash out all the cases.
        assert ValidHashNeighbors(table, e, j);
        assert ValidHashNeighbors(table, e, 0);
        if j+1 < |table| {
          assert ValidHashNeighbors(table, e, j+1);
        }

        assert ValidHashNeighbors(table', e, j);
      }
    }

    forall i | 0 <= i < |table|
    ensures ContiguousToEntry(table', i)
    {
      if table[i].Full? {
        assert ContiguousToEntry(table, i);
        if i < |table| - 1 {
          assert ContiguousToEntry(table, i+1);
        } else {
          assert ContiguousToEntry(table, 0);
        }

        var e := shift.end;
        var e1 := get_empty_slot_backwards(table, e);
        var e2 := get_empty_slot_forwards(table, shift.end);

        var e_next := (if e < |table| - 1 then e + 1 else 0);

        if e < i < e2 || i < e2 < e || e2 < e < i {
          hash_neighbor_transitive(table, e2, e_next, i);
          assert ContiguousToEntry(table', i);
        } else if (shift.start <= i < e) || (i < e < shift.start) || (e < shift.start <= i) {
          var h := hash(table'[i].key) as int;
          //var ip := (if i < |table| - 1 then i+1 else 0);
          //assert h == hash(table[ip].key) as int;
          assert 0 <= h <= |table| - 1;
          /*assert e1 < h <= ip || h <= ip < e1 || ip < e1 < h;
          assert h != ip;
          assert e1 < h < ip || h < ip < e1 || ip < e1 < h;
          assert e1 < h <= i || h <= i < e1 || i < e1 < h by {
            if e1 < h <= ip {
              assert e1 < h <= i;
            } else if h <= ip < e1 {
              assert h <= i < e1;
            } else if ip < e1 < h {
              if i == |table| - 1 {
                assert e1 < h <= i;
              } else {
                assert i < e1 < h;
              }
            }
          }*/

          assert ContiguousToEntry(table', i);
        } else {
          assert ContiguousToEntry(table', i);
        }
      }
    }
  }

  lemma GetValue_Remove_self(
      table: seq<Entry>, table': seq<Entry>,
      key: Key, shift: LeftShift)
  requires Inv(table)
  requires Remove(table, table', key, shift)
  ensures GetValue(table', key) == None
  {
  }

  lemma GetValue_Remove_other(
      table: seq<Entry>, table': seq<Entry>,
      key: Key, shift: LeftShift, other: Key)
  requires Inv(table)
  requires Remove(table, table', key, shift)
  requires other != key
  ensures GetValue(table', other) == GetValue(table, other)
  {
    if GetIndex(table, other).Some? {
      var j := GetIndex(table, other).value;
      //var k := (if j < |table| - 1 then j + 1 else 0);
      var k := (if j > 0 then j - 1 else |table| - 1);
      assert (table'[j].Full? && table'[j].key == other)
          || (table'[k].Full? && table'[k].key == other);
    } else if GetIndex(table', other).Some? {
    } else {
    }
  }

  // Insert key / value at a, shift a,...,b-1 to the right
  datatype RightShift = RightShift(start: int, end: int)

  predicate ApplyRightShift(table: seq<Entry>, table': seq<Entry>, key: Key, value: Value, shift: RightShift)
  {
    && 0 <= shift.start < |table|
    && 0 <= shift.end < |table|
    && |table'| == |table|

    && (shift.start <= shift.end ==>
      && (forall i | 0 <= i < shift.start :: table'[i] == table[i])
      && table'[shift.start] == Full(key, value)
      && (forall i | shift.start < i <= shift.end :: table'[i] == table[i-1])
      && (forall i | shift.end < i < |table'| :: table'[i] == table[i])
    )

    && (shift.start > shift.end ==>
      && table'[0] == table[|table| - 1]
      && (forall i | 0 < i <= shift.end :: table'[i] == table[i-1])
      && (forall i | shift.end < i < shift.start :: table'[i] == table[i])
      && table'[shift.start] == Full(key, value)
      && (forall i | shift.start < i < |table'| :: table'[i] == table[i-1])
    )
  }

  predicate ValidInBetweenInsertionPoint(table: seq<Entry>, i: int, h: uint32)
  {
    var j := if i > 0 then i - 1 else |table| - 1;
    && 0 <= i < |table|
    && table[i].Full?
    && table[j].Full?
    && (hash(table[j].key) <= h < hash(table[i].key)
     || h < hash(table[i].key) < hash(table[j].key)
     || hash(table[i].key) < hash(table[j].key) <= h)
  }

  predicate Insert(table: seq<Entry>, table': seq<Entry>, key: Key, value: Value, shift: RightShift)
  {
    && 0 <= shift.start < |table|
    && 0 <= shift.end < |table|

    // The next element must be empty
    && table[shift.end].Empty?

    && var h := hash(key) as int;

    && 0 <= h < |table|

    && (h <= shift.start <= shift.end
        || shift.start <= shift.end < h
        || shift.end < h <= shift.start)

    && (forall j | (h <= j < shift.end
        || 0 <= j <= shift.end < h
        || shift.end < h <= j < |table|) :: table[j].Full?)

    // key is not found in the range
    // (only have to check up to start of the shift)
    && (forall j | (h <= j <= shift.start
        || 0 <= j <= shift.start < h
        || shift.start < h <= j < |table|) :: table[j].Full? && table[j].key != key)

    // we put the new entry in the right spot:
    //
    // |-------|-------|-------|-------|-------|-------| Empty
    //   h               start                           end
    //
    //            h1       h2        
    //
    // If we're going to insert (k,v) at start with hashes h1 and h2 as shown,
    // we need h1 <= h < h2 (cyclically)
    // in which case we get h < start < end.
    //
    // If none of those work, then use start == end

    && (table[shift.start].Full? ==> (
      && shift.start != h
      && ValidInBetweenInsertionPoint(table, shift.start, hash(key))
    ))

    && (table[shift.start].Empty? ==> (
      && shift.start == shift.end
      && (forall j |
          (h < j < shift.end || j < shift.end < h || shift.end < h < j)
            :: !ValidInBetweenInsertionPoint(table, shift.start, hash(key)))
    ))

    && ApplyRightShift(table, table', key, value, shift)
  }

  lemma Insert_Inv(table: seq<Entry>, table': seq<Entry>, key: Key, value: Value, shift: RightShift)
  requires Inv(table)
  requires Insert(table, table', key, value, shift)
  ensures Inv(table')
  {
    assert KeysUnique(table') by {
      forall i | 0 <= i < |table| && table[i].Full? && table[i].key == key
      ensures false
      {
        assert ContiguousToEntry(table, shift.start);

        var j := if shift.start > 0 then shift.start - 1 else |table| - 1;
        assert ValidHashNeighbors(table, shift.end, j);

        assert ContiguousToEntry(table, i);
        hash_neighbor_transitive(table, shift.end, shift.start, i);
      }
    }

    forall e, j | 0 <= e < |table'| && 0 <= j < |table'|
    ensures ValidHashNeighbors(table', e, j)
    {
      var j' := if j > 0 then j - 1 else |table| - 1;
      var j1 := if j + 1 < |table| then j + 1 else 0;
      assert ValidHashNeighbors(table, e, j');
      assert ValidHashNeighbors(table, e, j);

      if table'[j].Full? && table'[j1].Full? {
        if j == shift.start {
          assert ValidHashNeighbors(table', e, j);
        } else if j1 == shift.start {
          assert ValidHashNeighbors(table', e, j);
        } else if j == shift.end {
          // Two previously-separate contiguous regions are now joining.
          assert ContiguousToEntry(table, j');
          assert ContiguousToEntry(table, j1);
          //assert hash(table[j1].key) as int == j1;
          assert ValidHashNeighbors(table', e, j);
        } else {
          assert ValidHashNeighbors(table', e, j);
        }
      }
    }

    forall j | 0 <= j < |table'|
    ensures ContiguousToEntry(table', j)
    {
      var j' := if j > 0 then j - 1 else |table| - 1;
      assert ContiguousToEntry(table, j);
      assert ContiguousToEntry(table, j');
    }

    assert ExistsEmptyEntry(table'); // TODO
  }
}
