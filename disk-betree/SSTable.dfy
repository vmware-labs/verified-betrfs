include "../lib/sequences.dfy"
include "../lib/maps.dfy"
include "../lib/total_order.dfy"
include "Message.dfy"
include "PivotBetreeSpec.dfy"
include "../lib/Marshalling/Native.s.dfy"

module SSTable {
  import opened ValueMessage`Internal
  import opened Lexicographic_Byte_Order
  import opened Options
  import opened Sequences
  import opened Maps
  import opened NativeTypes
  import ValueWithDefault`Internal
  import Uint64Order = Uint64_Order
  import BT = PivotBetreeSpec`Internal
  import P = PivotsLib
  import Native

  type String = seq<byte>
  type Key = String

  datatype SSTable = SSTable(starts: seq<uint64>, strings: String)

  function method Start(sst: SSTable, i: uint64) : uint64
    requires 0 <= i as int < |sst.starts|
  {
    sst.starts[i]
  }
  
  function method End(sst: SSTable, i: uint64) : uint64
    requires |sst.starts| < 0x1000_0000_0000_0000
    requires 0 <= i as int < |sst.starts|
    requires |sst.strings| < 0x1_0000_0000_0000_0000
  {
    if i + 1 < |sst.starts| as uint64 then
      sst.starts[i+1]
    else
      |sst.strings| as uint64
  }

  predicate Even(n: int)
  {
    n % 2 == 0
  }

  predicate WFSSTable(sst: SSTable)
  {
    && Uint64Order.IsSorted(sst.starts)
    && |sst.strings| < 0x1000_0000_0000_0000
    && |sst.starts| < 0x1000_0000_0000_0000
    && (|sst.starts| > 0 ==> (
      && sst.starts[0] == 0
      && 0 <= Last(sst.starts) as int <= |sst.strings|
    ))
    && (|sst.starts| == 0 ==> |sst.strings| == 0)
  }

  lemma LemmaStartEndIndices(sst: SSTable, i: int)
  requires WFSSTable(sst)
  requires 0 <= i < |sst.starts|
  ensures 0 <= Start(sst, i as uint64) as int <= End(sst, i as uint64) as int <= |sst.strings|
  {
    Uint64Order.reveal_IsSorted();
  }

  function method Entry(sst: SSTable, i: int) : String
  requires WFSSTable(sst)
  requires 0 <= i as int < |sst.starts|
  {
    LemmaStartEndIndices(sst, i);

    sst.strings[Start(sst, i as uint64)..End(sst, i as uint64)]
  }

  predicate {:opaque} KeysStrictlySorted(sst: SSTable)
  requires WFSSTable(sst)
  {
    forall i, j | 0 <= 2*i < 2*j < |sst.starts| ::
      lt(Entry(sst, 2*i), Entry(sst, 2*j))
  }

  lemma KeysStrictlySortedImplLt(sst: SSTable, i: int, j: int)
  requires WFSSTable(sst)
  requires KeysStrictlySorted(sst)
  requires 0 <= 2*i < 2*j < |sst.starts|
  ensures lt(Entry(sst, 2*i), Entry(sst, 2*j))
  {
    reveal_KeysStrictlySorted();
  }

  predicate WFSSTableMap(sst: SSTable)
  {
    && WFSSTable(sst)
    && Even(|sst.starts|)
    && KeysStrictlySorted(sst)
  }

  predicate SSTKeyMapsToValueAt(m: map<String, Message>, sst: SSTable, i: int)
  requires WFSSTableMap(sst)
  requires 0 <= 2*i < |sst.starts|
  {
    MapsTo(m, Entry(sst, 2*i), Define(Entry(sst, 1 + 2*i)))
  }

  lemma IPrefixLemma(sst: SSTable, k: int, m: map<String, Message>)
  requires WFSSTableMap(sst)
  requires 1 <= k
  requires 2*k <= |sst.starts|
  requires forall i | 0 <= i < k-1 :: SSTKeyMapsToValueAt(m, sst, i)
  requires forall key | key in m :: exists i :: 0 <= i < (k-1) && Entry(sst, 2*i) == key
  ensures forall i | 0 <= i < k :: SSTKeyMapsToValueAt(m[Entry(sst, 2*(k-1)) := Define(Entry(sst, 2*(k-1) + 1))], sst, i)
  {
    forall i | 0 <= i < k
    ensures SSTKeyMapsToValueAt(m[Entry(sst, 2*(k-1)) := Define(Entry(sst, 2*(k-1) + 1))], sst, i)
    {
      if (Entry(sst, 2*(k-1)) in m) {
        var i :| 0 <= i < (k-1) && Entry(sst, 2*i) == Entry(sst, 2*(k-1));
        reveal_KeysStrictlySorted();
      }
      if (i < k-1) {
        assert SSTKeyMapsToValueAt(m, sst, i);
      }
    }
  }

  function {:opaque} IPrefix(sst: SSTable, k: int) : (m : map<String, Message>)
  requires WFSSTableMap(sst)
  requires 0 <= 2*k <= |sst.starts|
  ensures forall i | 0 <= i < k :: SSTKeyMapsToValueAt(m, sst, i)
  ensures forall key | key in m :: exists i :: 0 <= i < k && Entry(sst, 2*i) == key
  {
    if k == 0 then
      map[]
    else (
      IPrefixLemma(sst, k, IPrefix(sst, k-1));

      IPrefix(sst, k-1)[Entry(sst, 2*(k-1)) := Define(Entry(sst, 2*(k-1) + 1))]
    )
  }

  function {:opaque} I(sst: SSTable) : (m : map<String, Message>)
  requires WFSSTableMap(sst)
  ensures forall i | 0 <= 2*i < |sst.starts| :: SSTKeyMapsToValueAt(m, sst, i)
  ensures forall key | key in m :: exists i :: 0 <= 2*i < |sst.starts| && Entry(sst, 2*i) == key
  {
    IPrefix(sst, |sst.starts| / 2)
  }

  function ISeq(ssts: seq<SSTable>) : (res : seq<map<String, Message>>)
  requires forall i | 0 <= i < |ssts| :: WFSSTableMap(ssts[i])
  ensures |res| == |ssts|
  ensures forall i | 0 <= i < |ssts| :: I(ssts[i]) == res[i]
  {
    if |ssts| == 0 then [] else ISeq(DropLast(ssts)) + [I(Last(ssts))]
  }

  function method {:opaque} Empty() : (sst : SSTable)
  ensures WFSSTableMap(sst)
  ensures I(sst) == map[]
  {
    reveal_I();
    Uint64Order.reveal_IsSorted();
    reveal_KeysStrictlySorted();

    SSTable([], [])
  }

  predicate method {:opaque} IsEmpty(sst: SSTable)
  requires WFSSTableMap(sst)
  ensures IsEmpty(sst) == (I(sst) == map[])
  {
    reveal_I();
    reveal_IPrefix();
    //assert |sst.starts| == 0 ==> I(sst) == map[];
    assert |sst.starts| > 0 ==> SSTKeyMapsToValueAt(I(sst), sst, 0);
    //assert |sst.starts| > 0 ==> I(sst) != map[];

    |sst.starts| == 0
  }

  lemma KeyNotInPrefix(sst: SSTable, i: int)
  requires WFSSTableMap(sst)
  requires 0 <= 2*i < |sst.starts|
  ensures Entry(sst, 2*i) !in IPrefix(sst, i)
  {
    if (Entry(sst, 2*i) in IPrefix(sst, i)) {
      var j :| 0 <= j < i && Entry(sst, 2*j) == Entry(sst, 2*i);
      reveal_KeysStrictlySorted();
    }
  }

  lemma SizeEqPrefix(sst: SSTable, i: int)
  requires WFSSTableMap(sst)
  requires 0 <= 2*i <= |sst.starts|
  ensures i == |IPrefix(sst, i)|
  {
    if (i == 0) {
      assert i == |IPrefix(sst, i)|;
    } else {
      SizeEqPrefix(sst, i-1);
      reveal_IPrefix();
      KeyNotInPrefix(sst, i-1);
      assert |IPrefix(sst, i)|
          == |IPrefix(sst, i-1)[Entry(sst, 2*(i-1)) := Define(Entry(sst, 2*(i-1) + 1))]|
          == |IPrefix(sst, i-1)| + 1;
      assert i == |IPrefix(sst, i)|;
    }
  }

  lemma SizeEq(sst: SSTable)
  requires WFSSTableMap(sst)
  ensures |sst.starts| == 2 * |I(sst)|
  {
    SizeEqPrefix(sst, |sst.starts|/2);
    reveal_I();
  }

  function method {:opaque} Size(sst: SSTable) : (n : uint64)
  requires WFSSTableMap(sst)
  ensures n as int == |I(sst)|
  ensures 2*n as int == |sst.starts|
  {
    SizeEq(sst);
    |sst.starts| as uint64 / 2
  }

  method Cmp(key: Key, sst: SSTable, i: uint64) returns (c: int32)
  requires WFSSTable(sst)
  requires 0 <= i as int < |sst.starts|
  ensures c == 0 || c == -1 || c == 1
  ensures c == 0 ==> key == Entry(sst, i as int)
  ensures c == -1 ==> lt(key, Entry(sst, i as int))
  ensures c == 1 ==> lt(Entry(sst, i as int), key)
  {
    reveal_seq_lte();
    Base_Order.reveal_lte();

    var j: uint64 := 0;
    var start: uint64 := Start(sst, i);
    var end: uint64 := End(sst, i);

    LemmaStartEndIndices(sst, i as int);
    assert |Entry(sst, i as int)| == end as int - start as int;

    while j as int < |key| && start + j < end
    invariant 0 <= j
    invariant j as int <= |key|
    invariant start as int + j as int <= end as int
    invariant seq_lte(key[j..], Entry(sst, i as int)[j..]) ==> seq_lte(key, Entry(sst, i as int))
    invariant seq_lte(Entry(sst, i as int)[j..], key[j..]) ==> seq_lte(Entry(sst, i as int), key)
    invariant key[..j] == Entry(sst, i as int)[..j];
    {
      if key[j] < sst.strings[start + j] {
        //assert key[j] == key[j..][0];
        //assert sst.strings[start + j] == Entry(sst, i)[j..][0];
        //assert key[j..][0] < Entry(sst, i)[j..][0];
        //assert Base_Order.lt(key[j..][0], Entry(sst, i)[j..][0]);
        //assert seq_lte(key[j..], Entry(sst, i)[j..]);
        return -1;
      }
      if key[j] > sst.strings[start + j] {
        return 1;
      }
      j := j + 1;
    }

    if start + j < end {
      assert j as int == |key|;
      return -1;
    }
    if j as int < |key| {
      assert start + j == end;
      return 1;
    }

    assert j as int == |key|;
    assert start + j == end;
    return 0;
  }

  method Cmp2(sst: SSTable, i: uint64, sst': SSTable, i': uint64) returns (c: int32)
  requires WFSSTable(sst)
  requires WFSSTable(sst')
  requires 0 <= i as int < |sst.starts|
  requires 0 <= i' as int < |sst'.starts|
  ensures c == 0 || c == -1 || c == 1
  ensures c == 0 ==> Entry(sst, i as int) == Entry(sst', i' as int)
  ensures c == -1 ==> lt(Entry(sst, i as int), Entry(sst', i' as int))
  ensures c == 1 ==> lt(Entry(sst', i' as int), Entry(sst, i as int))
  {
    reveal_seq_lte();
    Base_Order.reveal_lte();

    var j: uint64 := 0;
    var start: uint64 := Start(sst, i);
    var end: uint64 := End(sst, i);
    var start': uint64 := Start(sst', i');
    var end': uint64 := End(sst', i');

    LemmaStartEndIndices(sst, i as int);
    LemmaStartEndIndices(sst', i' as int);

    while start + j < end && start' + j < end'
    invariant 0 <= j
    invariant start as int + j as int <= end as int
    invariant start' as int + j as int <= end' as int
    invariant seq_lte(Entry(sst, i as int)[j..], Entry(sst', i' as int)[j..]) ==> seq_lte(Entry(sst, i as int), Entry(sst', i' as int))
    invariant seq_lte(Entry(sst', i' as int)[j..], Entry(sst, i as int)[j..]) ==> seq_lte(Entry(sst', i' as int), Entry(sst, i as int))
    invariant Entry(sst, i as int)[..j] == Entry(sst', i' as int)[..j]
    {
      if sst.strings[start + j] < sst'.strings[start' + j] {
        return -1;
      }
      if sst.strings[start + j] > sst'.strings[start' + j] {
        return 1;
      }

      assert seq_lte(Entry(sst, i as int)[j+1..], Entry(sst', i' as int)[j+1..]) ==> seq_lte(Entry(sst, i as int)[j..], Entry(sst', i' as int)[j..]);

      j := j + 1;
    }

    if start' + j < end' {
      assert start + j == end;
      return -1;
    }
    if start + j < end {
      assert start' + j == end';
      return 1;
    }

    assert start + j == end;
    assert start' + j == end';
    return 0;
  }

  lemma IndicesLtOfKeysLt(sst: SSTable, i: int, j: int)
  requires WFSSTableMap(sst)
  requires 0 <= 2*i < |sst.starts|
  requires 0 <= 2*j < |sst.starts|
  requires lt(Entry(sst, 2*i), Entry(sst, 2*j))
  ensures i < j
  {
    reveal_KeysStrictlySorted();
  }

  method Query(sst: SSTable, key: Key) returns (m: Option<Message>)
  requires WFSSTableMap(sst)
  ensures m.None? ==> key !in I(sst)
  ensures m.Some? ==> key in I(sst) && I(sst)[key] == m.value
  {
    var lo: uint64 := 0;
    var hi: uint64 := (|sst.starts| as uint64) / 2;

    while lo < hi
    invariant 0 <= 2*lo as int <= |sst.starts|
    invariant 0 <= 2*hi as int <= |sst.starts|
    invariant lo > 0 ==> lt(Entry(sst, 2*(lo-1) as int), key)
    invariant 2*hi as int < |sst.starts| ==> lt(key, Entry(sst, 2*hi as int))
    decreases hi as int - lo as int
    {
      var mid: uint64 := (lo + hi) / 2;
      var c := Cmp(key, sst, 2*mid);
      if c == 0 {
        m := Some(Define(Entry(sst, 2*mid as int + 1)));
        assert SSTKeyMapsToValueAt(I(sst), sst, mid as int);
        return;
      } else if (c == -1) {
        hi := mid;
      } else {
        lo := mid + 1;
      }
    }

    if (key in I(sst)) {
      ghost var j :| 0 <= 2*j < |sst.starts| && Entry(sst, 2*j as int) == key;
      if (lo > 0) { IndicesLtOfKeysLt(sst, lo as int - 1, j as int); }
      if (2*hi as int < |sst.starts|) { IndicesLtOfKeysLt(sst, j as int, hi as int); }
    }

    m := None;
  }

  /*
  method Merge(l: SSTable, r: SSTable) returns (c: SSTable)
  requires WFSSTableMap(l)
  requires WFSSTableMap(r)
  requires forall keyl, keyr | keyl in I(l) && keyr in I(r) :: lt(keyl, keyr)
  ensures I(c) == MapDisjointUnion(I(l), I(r))
  */

  predicate WFSSTableMapArrays(starts: array<uint64>, startsIdx: uint64, strings: array<byte>, stringsIdx: uint64)
  reads starts
  reads strings
  requires 0 <= startsIdx as int <= starts.Length
  requires 0 <= stringsIdx as int <= strings.Length
  {
    WFSSTableMap(SSTable(starts[..startsIdx], strings[..stringsIdx]))
  }

  function IArrays(starts: array<uint64>, startsIdx: uint64, strings: array<byte>, stringsIdx: uint64) : map<Key, Message>
  reads starts
  reads strings
  requires 0 <= startsIdx as int <= starts.Length
  requires 0 <= stringsIdx as int <= strings.Length
  requires WFSSTableMapArrays(starts, startsIdx, strings, stringsIdx)
  {
    I(SSTable(starts[..startsIdx], strings[..stringsIdx]))
  }


  lemma LemmaStartsArrayIsStrictlySorted(startsArray: array<uint64>, startsIdx: int, stringsIdx: int)
  requires 0 <= startsIdx
  requires startsIdx + 2 <= startsArray.Length
  requires Uint64Order.IsSorted(startsArray[..startsIdx])
  requires startsArray[startsIdx] as int == stringsIdx
  requires startsArray[startsIdx + 1] as int >= stringsIdx
  requires forall j | 0 <= j < startsIdx :: startsArray[j] as int <= stringsIdx
  ensures Uint64Order.IsSorted(startsArray[..startsIdx + 2])
  {
    Uint64Order.reveal_IsSorted();
  }

  lemma LemmaKeysArrayIsStrictlySorted(startsArray: array<uint64>,
      stringsArray: array<byte>, startsIdx: int, startsIdx': int, stringsIdx: int, stringsIdx': int, newKey: Key)
  requires 0 <= startsIdx
  requires startsIdx' == startsIdx + 2
  requires startsIdx' <= startsArray.Length
  requires startsArray[startsIdx] as int == stringsIdx
  requires startsArray[startsIdx + 1] as int >= stringsIdx
  requires stringsIdx <= stringsIdx'
  requires stringsIdx' as int <= stringsArray.Length
  requires WFSSTableMap(SSTable(startsArray[..startsIdx], stringsArray[..stringsIdx]))
  requires KeysStrictlySorted(SSTable(startsArray[..startsIdx], stringsArray[..stringsIdx]))
  requires forall key | key in IArrays(startsArray, startsIdx as uint64, stringsArray, stringsIdx as uint64) :: lt(key, newKey)
  requires Uint64Order.IsSorted(startsArray[..startsIdx + 2])
  requires startsArray[startsIdx+1] as int <= stringsArray.Length
  requires stringsArray[stringsIdx .. startsArray[startsIdx+1]] == newKey
  requires WFSSTable(SSTable(startsArray[..startsIdx'], stringsArray[..stringsIdx']))
  ensures KeysStrictlySorted(SSTable(startsArray[..startsIdx'], stringsArray[..stringsIdx']))
  {
    var sst := SSTable(startsArray[..startsIdx], stringsArray[..stringsIdx]);
    var sst' := SSTable(startsArray[..startsIdx'], stringsArray[..stringsIdx']);

    reveal_KeysStrictlySorted();

    forall i, j | 0 <= 2*i < 2*j < |sst'.starts|
    ensures lt(Entry(sst', 2*i), Entry(sst', 2*j))
    {
      if (2*j == |sst.starts|) {
        LemmaStartEndIndices(sst, 2*i);
        assert Entry(sst, 2*i) == Entry(sst', 2*i);

        assert SSTKeyMapsToValueAt(I(sst), sst, i);
        assert Entry(sst, 2*i) in I(sst);
        assert Entry(sst', 2*i) in I(sst);
        assert newKey == Entry(sst', 2*j);
        assert lt(Entry(sst', 2*i), Entry(sst', 2*j));
      } else {
        LemmaStartEndIndices(sst, 2*i);
        LemmaStartEndIndices(sst, 2*j);
        assert SSTKeyMapsToValueAt(I(sst), sst, i);
        assert Entry(sst, 2*i) == Entry(sst', 2*i);
        assert Entry(sst, 2*j) == Entry(sst', 2*j);
        assert lt(Entry(sst, 2*i), Entry(sst, 2*j));
        assert lt(Entry(sst', 2*i), Entry(sst', 2*j));
      }
    }
  }

  lemma KeysStrictlySortedImpliesLt(sst: SSTable, i: int, j: int)
  requires WFSSTable(sst)
  requires KeysStrictlySorted(sst)
  requires 0 <= 2*i;
  requires 2*i < 2*j
  requires 2*j < |sst.starts|
  ensures lt(Entry(sst, 2*i), Entry(sst, 2*j))
  {
    reveal_KeysStrictlySorted();
  }

  lemma KeysStrictlySortedImpliesLte(sst: SSTable, i: int, j: int)
  requires WFSSTable(sst)
  requires KeysStrictlySorted(sst)
  requires 0 <= 2*i;
  requires 2*i <= 2*j
  requires 2*j < |sst.starts|
  ensures lte(Entry(sst, 2*i), Entry(sst, 2*j))
  {
    reveal_KeysStrictlySorted();
  }

  lemma LemmaAugmentSSTable(sst: SSTable, sst': SSTable, key: Key, value: String)
  requires WFSSTableMap(sst)
  requires WFSSTableMap(sst')
  requires |sst'.starts| == |sst.starts| + 2
  requires |sst'.strings| >= |sst.strings|
  requires sst.starts == sst'.starts[..|sst.starts|]
  requires sst.strings == sst'.strings[..|sst.strings|]
  requires key == Entry(sst', |sst.starts|);
  requires value == Entry(sst', |sst.starts| + 1);
  requires sst'.starts[|sst.starts|] as int == |sst.strings|
  ensures I(sst') == I(sst)[key := Define(value)]
  {
    var a := I(sst');
    var b := I(sst)[key := Define(value)];

    forall k | k in a
    ensures k in b && a[k] == b[k]
    {
      var i :| 0 <= 2*i < |sst'.starts| && Entry(sst', 2*i) == k;
      if (2*i == |sst.starts|) {
        assert SSTKeyMapsToValueAt(I(sst'), sst', i);
        assert k in b;
        assert a[k] == b[k];
      } else {
        assert 2*i < |sst.starts|;

        var j := |sst.starts| / 2;
        assert 2*j == |sst.starts|;
        KeysStrictlySortedImpliesLt(sst', i, j);
        assert lt(Entry(sst', 2*i), Entry(sst', 2*j));
        assert k != key;

        assert SSTKeyMapsToValueAt(I(sst), sst, i);
        assert Entry(sst, 2*i) in I(sst);

        assert Start(sst, 2*i as uint64) == Start(sst', 2*i as uint64);
        assert End(sst, 2*i as uint64) == End(sst', 2*i as uint64);
        LemmaStartEndIndices(sst, 2*i);
        //assert End(sst, 2*i as uint64) as int <= |sst.strings|;

        assert 2*i + 1 < |sst.starts|;
        assert Start(sst, 2*i as uint64 + 1) == Start(sst', 2*i as uint64 + 1);
        assert End(sst, 2*i as uint64 + 1) == End(sst', 2*i as uint64 + 1);
        LemmaStartEndIndices(sst, 2*i+1);
        //assert End(sst, 2*i+1 as uint64) as int <= |sst.strings|;

        assert Entry(sst, 2*i) == Entry(sst', 2*i);
        assert k in I(sst);
        assert I(sst)[k] == Define(Entry(sst, 2*i+1));
        assert SSTKeyMapsToValueAt(I(sst'), sst', i);
        assert I(sst')[k] == Define(Entry(sst', 2*i+1));
        assert I(sst)[k] == I(sst')[k];
        assert k in b;
        assert a[k] == b[k];
      }
    }

    forall k | k in b
    ensures k in a
    {
      var j := |sst.starts| / 2;
      assert 2*j == |sst.starts|;

      if (k == key) {
        assert k == Entry(sst', 2*j);
        assert SSTKeyMapsToValueAt(I(sst'), sst', j);
        assert Entry(sst', 2*j) in I(sst');
        assert k in I(sst');
      } else {
        assert k in I(sst);

        var i :| 0 <= 2*i < |sst.starts| && Entry(sst, 2*i) == k;
        assert 2*i < 2*j;

        assert Start(sst, 2*i as uint64) == Start(sst', 2*i as uint64);
        assert End(sst, 2*i as uint64) == End(sst', 2*i as uint64);
        LemmaStartEndIndices(sst, 2*i);

        assert Entry(sst, 2*i) == Entry(sst', 2*i);
        assert SSTKeyMapsToValueAt(I(sst'), sst', i);
        assert k in I(sst');
      }
    }

    assert a.Keys == b.Keys;

    assert forall k | k in b :: k in a && a[k] == b[k];

    assert a == b;
  }

  method WriteKeyValue(startsArray: array<uint64>, stringsArray: array<byte>, startsIdx: uint64, stringsIdx: uint64, sst: SSTable, i: uint64)
  returns (startsIdx': uint64, stringsIdx': uint64)
  modifies startsArray
  modifies stringsArray
  requires WFSSTableMap(sst)
  requires 0 <= i
  requires i as int + 1 < |sst.starts|
  requires 0 <= startsIdx
  requires startsIdx as int + 2 <= startsArray.Length
  requires 0 <= stringsIdx
  requires stringsIdx as int <= stringsArray.Length
  requires stringsIdx as int + End(sst, i+1) as int - Start(sst, i) as int <= stringsArray.Length
  requires WFSSTableMapArrays(startsArray, startsIdx, stringsArray, stringsIdx)
  requires forall key | key in IArrays(startsArray, startsIdx, stringsArray, stringsIdx) :: lt(key, Entry(sst, i as int))
  requires stringsArray.Length < 0x1000_0000_0000_0000
  requires startsArray.Length < 0x1000_0000_0000_0000
  requires startsIdx == 0 ==> stringsIdx == 0
  ensures 0 <= startsIdx' as int <= startsArray.Length
  ensures 0 <= stringsIdx' as int <= stringsArray.Length
  ensures startsIdx' == startsIdx + 2
  ensures stringsIdx' as int == stringsIdx as int + End(sst, i+1) as int - Start(sst, i) as int;
  ensures WFSSTableMapArrays(startsArray, startsIdx', stringsArray, stringsIdx')
  ensures IArrays(startsArray, startsIdx', stringsArray, stringsIdx')
       == old(IArrays(startsArray, startsIdx, stringsArray, stringsIdx))[Entry(sst, i as int) := Define(Entry(sst, i as int + 1))]
  {
    LemmaStartEndIndices(sst, i as int);
    LemmaStartEndIndices(sst, i as int + 1);
    forall j | 0 <= j < startsIdx
    ensures startsArray[j] <= stringsIdx
    {
      Uint64Order.reveal_IsSorted();
    }

    startsArray[startsIdx] := stringsIdx;
    startsArray[startsIdx + 1] := stringsIdx + (End(sst, i) - Start(sst, i));
    startsIdx' := startsIdx + 2;

    Native.Arrays.CopySeqIntoArray(sst.strings, Start(sst, i), stringsArray, stringsIdx, End(sst, i+1) - Start(sst, i));
    stringsIdx' := stringsIdx + End(sst, i+1) - Start(sst, i);

    LemmaStartsArrayIsStrictlySorted(startsArray, startsIdx as int, stringsIdx as int);

    assert startsArray[..startsIdx] == old(startsArray[..startsIdx]);
    assert stringsArray[..stringsIdx] == old(stringsArray[..stringsIdx]);
    assert old(IArrays(startsArray, startsIdx, stringsArray, stringsIdx))
        == IArrays(startsArray, startsIdx, stringsArray, stringsIdx);
    assert WFSSTableMapArrays(startsArray, startsIdx, stringsArray, stringsIdx);

    LemmaKeysArrayIsStrictlySorted(startsArray, stringsArray, startsIdx as int,
        startsIdx' as int, stringsIdx as int, stringsIdx' as int, Entry(sst, i as int));

    assert sst.strings[Start(sst, i) .. End(sst, i)]
        == stringsArray[startsArray[startsIdx] .. startsArray[startsIdx + 1]];

    assert sst.strings[Start(sst, i + 1) .. End(sst, i + 1)]
        == stringsArray[startsArray[startsIdx + 1] .. stringsIdx'];

    LemmaAugmentSSTable(
        SSTable(startsArray[..startsIdx], stringsArray[..stringsIdx]),
        SSTable(startsArray[..startsIdx'], stringsArray[..stringsIdx']),
        Entry(sst, i as int),
        Entry(sst, i as int + 1)
    );
  }

  method MaxLens(s: seq<SSTable>)
  returns (startsLen : uint64, stringsLen: uint64)
  requires forall i | 0 <= i < |s| :: |s[i].strings| < 0x800_0000_0000_0000
  requires forall i | 0 <= i < |s| :: |s[i].starts| < 0x800_0000_0000_0000
  ensures forall i | 0 <= i < |s| :: |s[i].starts| <= startsLen as int
  ensures forall i | 0 <= i < |s| :: |s[i].strings| <= stringsLen as int
  ensures startsLen < 0x800_0000_0000_0000
  ensures stringsLen < 0x800_0000_0000_0000
  {
    startsLen := 0;
    stringsLen := 0;

    var j := 0;
    while j < |s|
    invariant j <= |s|
    invariant forall i | 0 <= i < j :: |s[i].starts| <= startsLen as int
    invariant forall i | 0 <= i < j :: |s[i].strings| <= stringsLen as int
    invariant startsLen < 0x800_0000_0000_0000
    invariant stringsLen < 0x800_0000_0000_0000
    {
      if |s[j].starts| as uint64 > startsLen {
        startsLen := |s[j].starts| as uint64;
      }
      if |s[j].strings| as uint64 > stringsLen {
        stringsLen := |s[j].strings| as uint64;
      }

      j := j + 1;
    }
  }
  
  lemma LemmaWFEmptyArrays(startsArray: array<uint64>, stringsArray: array<byte>)
  ensures WFSSTableMapArrays(startsArray, 0, stringsArray, 0)
  ensures IArrays(startsArray, 0, stringsArray, 0) == map[]
  {
    Uint64Order.reveal_IsSorted();
    reveal_KeysStrictlySorted();
  }

  lemma AddMessagesToBucketAddParentKey(pivots: seq<Key>, childrenIdx: int, m: map<Key, Message>, m': map<Key, Message>, key: Key, msg: Message, parent: map<Key, Message>, child: map<Key, Message>)
  requires P.WFPivots(pivots)
  requires m' == m[key := msg]
  requires key !in parent
  requires key !in child
  requires m == BT.AddMessagesToBucket(pivots, childrenIdx, child, parent)
  requires P.Route(pivots, key) == childrenIdx
  requires msg != IdentityMessage()
  ensures m' == BT.AddMessagesToBucket(pivots, childrenIdx, child, parent[key := msg])
  {
  }

  lemma AddMessagesToBucketAddChildKey(pivots: seq<Key>, childrenIdx: int, m: map<Key, Message>, m': map<Key, Message>, key: Key, msg: Message, parent: map<Key, Message>, child: map<Key, Message>)
  requires P.WFPivots(pivots)
  requires m' == m[key := msg]
  requires key !in parent
  requires key !in child
  requires m == BT.AddMessagesToBucket(pivots, childrenIdx, child, parent)
  requires P.Route(pivots, key) == childrenIdx
  requires msg != IdentityMessage()
  ensures m' == BT.AddMessagesToBucket(pivots, childrenIdx, child[key := msg], parent)
  {
    /*
    var amtb := BT.AddMessagesToBucket(pivots, childrenIdx, child[key := msg], parent);
    forall k | k in m'
    ensures k in amtb
    ensures m'[k] == amtb[k]
    {
      if (k == key) {
        var childBucket := child[key := msg];
        assert key in (childBucket.Keys + parent.Keys);
        assert P.Route(pivots, key) == childrenIdx;
        assert k in amtb;
        assert m'[k] == amtb[k];
      } else {
        assert k in amtb;
        assert m'[k] == amtb[k];
      }
    }
    assert m' == amtb;
    */
  }

  lemma AddMessagesToBucketAddParentAndChildKey(pivots: seq<Key>, childrenIdx: int, m: map<Key, Message>, m': map<Key, Message>, key: Key, msgParent: Message, msgChild: Message, parent: map<Key, Message>, child: map<Key, Message>)
  requires P.WFPivots(pivots)
  requires m' == m[key := ValueMessage.Merge(msgParent, msgChild)]
  requires key !in parent
  requires key !in child
  requires m == BT.AddMessagesToBucket(pivots, childrenIdx, child, parent)
  requires P.Route(pivots, key) == childrenIdx
  requires ValueMessage.Merge(msgParent, msgChild) != IdentityMessage()
  ensures m' == BT.AddMessagesToBucket(pivots, childrenIdx, child[key := msgChild], parent[key := msgParent])
  {
  }

  lemma LemmaFlushAddParentKey(pivots: seq<Key>, childrenIdx: int, m: map<Key, Message>, m': map<Key, Message>, parent: SSTable, child: SSTable, parentIdx: int, childIdx: int)
  requires P.WFPivots(pivots)
  requires WFSSTableMap(parent)
  requires WFSSTableMap(child)
  requires 0 <= childrenIdx <= |pivots|
  requires 0 <= 2*parentIdx < |parent.starts|
  requires 0 <= 2*childIdx <= |child.starts|
  requires m' == m[Entry(parent, 2*parentIdx as int) := Define(Entry(parent, 2*parentIdx as int + 1))]
  requires m == BT.AddMessagesToBucket(pivots, childrenIdx, IPrefix(child, childIdx as int), IPrefix(parent, parentIdx as int))
  requires forall key | key in IPrefix(child, childIdx as int) :: lt(key, Entry(parent, 2*parentIdx as int))
  requires childrenIdx > 0 ==> lte(pivots[childrenIdx - 1], Entry(parent, 2*parentIdx as int))
  requires forall key | key in I(child) :: P.Route(pivots, key) == childrenIdx
  requires 2*childIdx < |child.starts| ==> lt(Entry(parent, 2*parentIdx as int), Entry(child, 2*childIdx as int))
  requires 2*childIdx == |child.starts| && childrenIdx < |pivots| ==> lt(Entry(parent, 2*parentIdx as int), pivots[childrenIdx])
  ensures m' == BT.AddMessagesToBucket(pivots, childrenIdx, IPrefix(child, childIdx as int), IPrefix(parent, parentIdx as int + 1))
  {
    var key := Entry(parent, 2*parentIdx as int);
    assert key !in IPrefix(child, childIdx as int);
    KeyNotInPrefix(parent, parentIdx);

    if (2*childIdx as int < |child.starts|) {
      assert SSTKeyMapsToValueAt(I(child), child, childIdx);
      //assert P.Route(pivots, Entry(child, 2*childIdx as int)) == childrenIdx;
    }
    P.RouteIs(pivots, key, childrenIdx);

    AddMessagesToBucketAddParentKey(pivots, childrenIdx, m, m', 
        Entry(parent, 2*parentIdx as int),
        Define(Entry(parent, 2*parentIdx as int + 1)),
        IPrefix(parent, parentIdx as int),
        IPrefix(child, childIdx as int));
    reveal_IPrefix();
    //assert IPrefix(parent, parentIdx as int + 1) == IPrefix(parent, parentIdx)[Entry(parent, 2*parentIdx as int) := Define(Entry(parent, 2*parentIdx as int + 1))];
  }

  lemma LemmaFlushAddChildKey(pivots: seq<Key>, childrenIdx: int, m: map<Key, Message>, m': map<Key, Message>, parent: SSTable, child: SSTable, parentIdx: int, childIdx: int)
  requires P.WFPivots(pivots)
  requires WFSSTableMap(parent)
  requires WFSSTableMap(child)
  requires 0 <= childrenIdx <= |pivots|
  requires 0 <= 2*parentIdx <= |parent.starts|
  requires 0 <= 2*childIdx < |child.starts|
  requires m' == m[Entry(child, 2*childIdx as int) := Define(Entry(child, 2*childIdx as int + 1))]
  requires m == BT.AddMessagesToBucket(pivots, childrenIdx, IPrefix(child, childIdx as int), IPrefix(parent, parentIdx as int))
  requires forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, Entry(child, 2*childIdx as int))
  requires forall key | key in I(child) :: P.Route(pivots, key) == childrenIdx
  ensures m' == BT.AddMessagesToBucket(pivots, childrenIdx, IPrefix(child, childIdx as int + 1), IPrefix(parent, parentIdx as int))
  {
    var key := Entry(child, 2*childIdx as int);
    assert key !in IPrefix(parent, parentIdx as int);
    KeyNotInPrefix(child, childIdx);

    assert SSTKeyMapsToValueAt(I(child), child, childIdx);
    assert P.Route(pivots, key) == childrenIdx;

    AddMessagesToBucketAddChildKey(pivots, childrenIdx, m, m', 
        Entry(child, 2*childIdx as int),
        Define(Entry(child, 2*childIdx as int + 1)),
        IPrefix(parent, parentIdx as int),
        IPrefix(child, childIdx as int));
    reveal_IPrefix();
  }

  lemma {:fuel P.Route,0} {:fuel BT.AddMessagesToBucket,0} LemmaFlushAddParentAndChildKey(pivots: seq<Key>, childrenIdx: int, m: map<Key, Message>, m': map<Key, Message>, parent: SSTable, child: SSTable, parentIdx: int, childIdx: int)
  requires P.WFPivots(pivots)
  requires WFSSTableMap(parent)
  requires WFSSTableMap(child)
  requires 0 <= childrenIdx <= |pivots|
  requires 0 <= 2*parentIdx < |parent.starts|
  requires 0 <= 2*childIdx < |child.starts|
  requires m' == m[Entry(child, 2*childIdx as int) := Define(Entry(parent, 2*parentIdx as int + 1))]
  requires m == BT.AddMessagesToBucket(pivots, childrenIdx, IPrefix(child, childIdx as int), IPrefix(parent, parentIdx as int))
  requires Entry(child, 2*childIdx as int) == Entry(parent, 2*parentIdx as int)
  requires forall key | key in I(child) :: P.Route(pivots, key) == childrenIdx
  ensures m' == BT.AddMessagesToBucket(pivots, childrenIdx, IPrefix(child, childIdx as int + 1), IPrefix(parent, parentIdx as int + 1))
  {
    var key := Entry(child, 2*childIdx as int);
    KeyNotInPrefix(parent, parentIdx);
    KeyNotInPrefix(child, childIdx);

    assert SSTKeyMapsToValueAt(I(child), child, childIdx);
    assert P.Route(pivots, key) == childrenIdx;

    AddMessagesToBucketAddParentAndChildKey(pivots, childrenIdx, m, m', 
        Entry(child, 2*childIdx as int),
        Define(Entry(parent, 2*parentIdx as int + 1)),
        Define(Entry(child, 2*childIdx as int + 1)),
        IPrefix(parent, parentIdx as int),
        IPrefix(child, childIdx as int));
    reveal_IPrefix();
  }

  function Boundary(sst: SSTable, i: uint64) : int
  requires WFSSTable(sst)
  requires 0 <= i as int <= |sst.starts|
  {
    if i as int < |sst.starts| then sst.starts[i] as int else |sst.strings|
  }

  lemma BoundaryLe(sst: SSTable, i: uint64, j: uint64)
  requires WFSSTable(sst)
  requires 0 <= i as int <= j as int <= |sst.starts|
  ensures Boundary(sst, i) <= Boundary(sst, j)
  {
    Uint64Order.reveal_IsSorted();
  }

  lemma KeyInPrefixImpliesLt(key: Key, sst: SSTable, idx: int)
  requires WFSSTableMap(sst)
  requires 0 <= 2*idx < |sst.starts|
  requires key in IPrefix(sst, idx)
  ensures lt(key, Entry(sst, 2*idx))
  {
    var j :| 0 <= j < idx && key == Entry(sst, 2*j);
    reveal_KeysStrictlySorted();
  }
  
  lemma LemmaIArrayKeysLt(parent: SSTable, child: SSTable, childrenIdx: int, parentIdx: int, childIdx: int, pivots: seq<Key>,
      startsArray: array<uint64>, startsIdx: uint64, stringsArray: array<byte>, stringsIdx: uint64)
  requires WFSSTableMap(parent)
  requires WFSSTableMap(child)
  requires P.WFPivots(pivots)
  requires 0 <= childrenIdx <= |pivots|
  requires 0 <= 2*parentIdx <= |parent.starts|
  requires 0 <= 2*childIdx <= |child.starts|
  requires 0 <= startsIdx as int <= startsArray.Length
  requires 0 <= stringsIdx as int <= stringsArray.Length
  requires WFSSTableMapArrays(startsArray, startsIdx, stringsArray, stringsIdx)
  requires 2*parentIdx < |parent.starts| ==> forall key | key in IPrefix(child, childIdx) :: lt(key, Entry(parent, 2*parentIdx))
  requires 2*childIdx < |child.starts| ==> forall key | key in IPrefix(parent, parentIdx) :: lt(key, Entry(child, 2*childIdx))
  requires IArrays(startsArray, startsIdx, stringsArray, stringsIdx) == BT.AddMessagesToBucket(pivots, childrenIdx, IPrefix(child, childIdx), IPrefix(parent, parentIdx))
  ensures 2*parentIdx < |parent.starts| ==> forall key | key in IArrays(startsArray, startsIdx, stringsArray, stringsIdx) :: lt(key, Entry(parent, 2*parentIdx))
  ensures 2*childIdx < |child.starts| ==> forall key | key in IArrays(startsArray, startsIdx, stringsArray, stringsIdx) :: lt(key, Entry(child, 2*childIdx))
  {
    if (2*parentIdx < |parent.starts|) {
      forall key | key in IArrays(startsArray, startsIdx, stringsArray, stringsIdx)
      ensures lt(key, Entry(parent, 2*parentIdx))
      {
        assert key in IPrefix(child, childIdx) || key in IPrefix(parent, parentIdx);
        if (key in IPrefix(child, childIdx)) {
          assert lt(key, Entry(parent, 2*parentIdx));
        } else {
          KeyInPrefixImpliesLt(key, parent, parentIdx);
          assert lt(key, Entry(parent, 2*parentIdx));
        }
      }
    }
    if (2*childIdx < |child.starts|) {
      forall key | key in IArrays(startsArray, startsIdx, stringsArray, stringsIdx)
      ensures lt(key, Entry(child, 2*childIdx))
      {
        assert key in IPrefix(child, childIdx) || key in IPrefix(parent, parentIdx);
        if (key in IPrefix(child, childIdx)) {
          KeyInPrefixImpliesLt(key, child, childIdx);
          assert lt(key, Entry(child, 2*childIdx));
        } else {
          assert lt(key, Entry(child, 2*childIdx));
        }
      }
    }
  }

  lemma PivotLeFirstChildOfNextBucket(childrenIdx: int, children: seq<SSTable>, pivots: seq<Key>)
  requires P.WFPivots(pivots)
  requires forall i | 0 <= i < |children| :: WFSSTableMap(children[i])
  requires forall i, key | 0 <= i < |children| && key in I(children[i]) :: P.Route(pivots, key) == i
  requires 0 <= childrenIdx <= |pivots|
  requires |children| == |pivots| + 1
  ensures childrenIdx+1 < |children| && 0 < |children[childrenIdx+1].starts| ==>
    lte(pivots[childrenIdx], Entry(children[childrenIdx+1], 0))
  {
    if (childrenIdx+1 < |children| && 0 < |children[childrenIdx+1].starts|) {
      assert SSTKeyMapsToValueAt(I(children[childrenIdx+1]), children[childrenIdx+1], 0);
      assert P.Route(pivots, Entry(children[childrenIdx+1], 0)) == childrenIdx+1;
    }
  }

  lemma CurChildLtPivot(childrenIdx: int, childIdx: int, children: seq<SSTable>, pivots: seq<Key>)
  requires P.WFPivots(pivots)
  requires forall i | 0 <= i < |children| :: WFSSTableMap(children[i])
  requires forall i, key | 0 <= i < |children| && key in I(children[i]) :: P.Route(pivots, key) == i
  requires 0 <= childrenIdx <= |pivots|
  requires childrenIdx < |children|
  requires 0 <= 2*childIdx <= |children[childrenIdx].starts|
  requires |children| == |pivots| + 1
  ensures childrenIdx+1 < |children| && 2*childIdx < |children[childrenIdx].starts| ==>
    lt(Entry(children[childrenIdx], 2*childIdx), pivots[childrenIdx])
  {
    if childrenIdx+1 < |children| && 2*childIdx < |children[childrenIdx].starts| {
      assert SSTKeyMapsToValueAt(I(children[childrenIdx]), children[childrenIdx], childIdx);
      assert P.Route(pivots, Entry(children[childrenIdx], 2*childIdx)) == childrenIdx;
    }
  }

  lemma EmptyAddMessagesToBucket(pivots: seq<Key>)
  requires P.WFPivots(pivots)
  ensures BT.AddMessagesToBucket(pivots, 0, map[], map[]) == map[]
  {
  }

  lemma EmptyAddMessagesToBucketWhenAllKeysInParentAreLt(pivots: seq<Key>, i: int, m: map<Key, Message>)
  requires P.WFPivots(pivots)
  requires 0 <= i < |pivots|
  requires forall key | key in m :: lt(key, pivots[i])
  ensures BT.AddMessagesToBucket(pivots, i+1, map[], m) == map[]
  {
  }

  lemma AddMessagesToBucketEqIfEqInRange(pivots: seq<Key>, i: int, child: map<Key, Message>, p1: map<Key, Message>, p2: map<Key, Message>)
  requires P.WFPivots(pivots)
  requires 0 <= i <= |pivots|
  requires forall key | P.Route(pivots, key) == i :: MapsAgreeOnKey(p1, p2, key)
  ensures BT.AddMessagesToBucket(pivots, i, child, p1)
       == BT.AddMessagesToBucket(pivots, i, child, p2)
  {
  }

  lemma LemmaAddMessagesToBucketsAugment(
    pivots: seq<Key>,
    parent: SSTable,
    children: seq<SSTable>,
    childrenIdx: int,
    childIdx: int,
    parentIdx: int,
    res: seq<SSTable>,
    res': seq<SSTable>,
    startsArray: array<uint64>,
    stringsArray: array<byte>,
    startsIdx: uint64,
    stringsIdx: uint64)
  requires P.WFPivots(pivots)
  requires WFSSTableMap(parent)
  requires forall i | 0 <= i < |children| :: WFSSTableMap(children[i])
  requires 0 <= startsIdx as int <= startsArray.Length
  requires 0 <= stringsIdx as int <= stringsArray.Length
  requires WFSSTableMapArrays(startsArray, startsIdx, stringsArray, stringsIdx)
  requires res' == res + [SSTable(startsArray[..startsIdx], stringsArray[..stringsIdx])];
  requires 0 <= childrenIdx <= |pivots|
  requires |children| == |pivots| + 1
  requires 2*childIdx == |children[childrenIdx].starts|
  requires 0 <= 2*parentIdx <= |parent.starts|
  requires |res| == childrenIdx
  requires IArrays(startsArray, startsIdx, stringsArray, stringsIdx)
       == BT.AddMessagesToBucket(pivots, childrenIdx, IPrefix(children[childrenIdx], childIdx), IPrefix(parent, parentIdx))
  requires |res| == childrenIdx
  requires  forall i | 0 <= i < |res| :: WFSSTableMap(res[i])
  requires ISeq(res) == BT.AddMessagesToBuckets(pivots, |res|, ISeq(children), I(parent))
  requires 2*parentIdx < |parent.starts| && childrenIdx < |pivots| ==> lte(pivots[childrenIdx], Entry(parent, 2*parentIdx))
  requires childrenIdx == |pivots| ==> 2*parentIdx == |parent.starts|
  ensures forall i | 0 <= i < |res'| :: WFSSTableMap(res'[i])
  ensures ISeq(res') == BT.AddMessagesToBuckets(pivots, |res'|, ISeq(children), I(parent))
  {
    forall key | P.Route(pivots, key) == childrenIdx
    ensures MapsAgreeOnKey(I(parent), IPrefix(parent, parentIdx), key)
    {
      if (key in IPrefix(parent, parentIdx)) {
        var i :| 0 <= i < parentIdx && Entry(parent, 2*i) == key;
        assert SSTKeyMapsToValueAt(IPrefix(parent, parentIdx), parent, i);
        assert SSTKeyMapsToValueAt(I(parent), parent, i);
      } else if (key in I(parent)) {
        var i :| 0 <= 2*i < |parent.starts| && Entry(parent, 2*i) == key;
        assert SSTKeyMapsToValueAt(I(parent), parent, i);
        if (i < parentIdx) {
          assert SSTKeyMapsToValueAt(IPrefix(parent, parentIdx), parent, i);
          assert false;
        } else {
          assert childrenIdx < |pivots|;
          assert 2*parentIdx < |parent.starts|;
          assert lt(Entry(parent, 2*i), pivots[childrenIdx]);
          assert lte(pivots[childrenIdx], Entry(parent, 2*parentIdx));
          KeysStrictlySortedImpliesLte(parent, parentIdx, i);
          assert false;
        }
      }
    }
    AddMessagesToBucketEqIfEqInRange(pivots, childrenIdx, I(children[childrenIdx]), I(parent), IPrefix(parent, parentIdx));

    reveal_I();
    assert IPrefix(children[childrenIdx], childIdx) == I(children[childrenIdx]);

    assert BT.AddMessagesToBucket(pivots, childrenIdx, IPrefix(children[childrenIdx], childIdx), IPrefix(parent, parentIdx))
        == BT.AddMessagesToBucket(pivots, childrenIdx, I(children[childrenIdx]), IPrefix(parent, parentIdx))
        == BT.AddMessagesToBucket(pivots, childrenIdx, I(children[childrenIdx]), I(parent));
  }

  method {:fuel P.Route,0} {:fuel BT.AddMessagesToBucket,0} DoFlush(parent: SSTable, children: seq<SSTable>, pivots: seq<Key>)
  returns (res : seq<SSTable>)
  requires WFSSTableMap(parent)
  requires P.WFPivots(pivots)
  requires |parent.strings| < 0x800_0000_0000_0000
  requires |parent.starts| < 0x800_0000_0000_0000
  requires forall i | 0 <= i < |children| :: WFSSTableMap(children[i])
  requires forall i | 0 <= i < |children| :: |children[i].strings| < 0x800_0000_0000_0000
  requires forall i | 0 <= i < |children| :: |children[i].starts| < 0x800_0000_0000_0000
  requires |children| == |pivots| + 1
  requires forall i, key | 0 <= i < |children| && key in I(children[i]) :: P.Route(pivots, key) == i
  ensures forall i | 0 <= i < |res| :: WFSSTableMap(res[i])
  ensures ISeq(res) == BT.AddMessagesToBuckets(pivots, |children|, ISeq(children), I(parent))
  {
    var maxChildStartsLen: uint64, maxChildStringsLen: uint64 := MaxLens(children);
    var startsArray : array<uint64> := new uint64[maxChildStartsLen + |parent.starts| as uint64];
    var stringsArray : array<byte> := new byte[maxChildStringsLen + |parent.strings| as uint64];
    var startsIdx: uint64 := 0;
    var stringsIdx: uint64 := 0;

    res := [];

    LemmaWFEmptyArrays(startsArray, stringsArray);
    EmptyAddMessagesToBucket(pivots);

    var parentIdx: uint64 := 0;
    var childrenIdx: int := 0;
    var childIdx: uint64 := 0;

    reveal_IPrefix();

    while childrenIdx < |children|

    invariant 0 <= 2*parentIdx as int <= |parent.starts|
    invariant 0 <= childrenIdx <= |children|
    invariant childrenIdx < |children| ==> 0 <= 2*childIdx as int <= |children[childrenIdx].starts|
    invariant 0 <= startsIdx as int <= startsArray.Length
    invariant 0 <= stringsIdx as int <= stringsArray.Length
    invariant WFSSTableMapArrays(startsArray, startsIdx, stringsArray, stringsIdx)

    invariant startsIdx as int <= 2 * (childIdx as int + parentIdx as int)
    invariant childrenIdx < |children| ==> stringsIdx as int <= Boundary(children[childrenIdx], 2*childIdx) + Boundary(parent, 2*parentIdx)
    invariant startsIdx == 0 ==> stringsIdx == 0

    invariant childrenIdx < |children| ==> 2*parentIdx as int < |parent.starts| ==>
        forall key | key in IPrefix(children[childrenIdx], childIdx as int) :: lt(key, Entry(parent, 2*parentIdx as int))
    invariant 0 < childrenIdx < |children| && 2*parentIdx as int < |parent.starts| ==> lte(pivots[childrenIdx - 1], Entry(parent, 2*parentIdx as int))

    invariant childrenIdx < |children| ==> 2*childIdx as int < |children[childrenIdx].starts| ==>
        forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, Entry(children[childrenIdx], 2*childIdx as int))

    invariant childrenIdx < |children| - 1 ==>
        forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, pivots[childrenIdx])

    invariant childrenIdx < |children| ==>
          IArrays(startsArray, startsIdx, stringsArray, stringsIdx)
       == BT.AddMessagesToBucket(pivots, childrenIdx, IPrefix(children[childrenIdx], childIdx as int), IPrefix(parent, parentIdx as int))
    invariant |res| == childrenIdx
    invariant forall i | 0 <= i < |res| :: WFSSTableMap(res[i])
    invariant ISeq(res) == BT.AddMessagesToBuckets(pivots, |res|, ISeq(children), I(parent))

    decreases |children| - childrenIdx as int
    decreases (|parent.starts| - 2*parentIdx as int) + (if childrenIdx as int < |children| then |children[childrenIdx].starts| - 2*childIdx as int else 0)

    {
      ghost var oldIArray := IArrays(startsArray, startsIdx, stringsArray, stringsIdx);
      assert |children[childrenIdx].starts| + |parent.starts| <= startsArray.Length;
      assert |children[childrenIdx].strings| + |parent.strings| <= stringsArray.Length;
      if (childIdx > 0) {
        LemmaStartEndIndices(children[childrenIdx], 2*childIdx as int - 1);
      }
      assert Boundary(children[childrenIdx], 2*childIdx) <= |children[childrenIdx].strings|;
      if (parentIdx > 0) {
        LemmaStartEndIndices(parent, 2*parentIdx as int - 1);
      }
      assert Boundary(parent, 2*parentIdx) <= |parent.strings|;
      if (2*(childIdx as int + 1) <= |children[childrenIdx].starts|) {
        LemmaStartEndIndices(children[childrenIdx], 2*childIdx as int + 1);
        assert Boundary(children[childrenIdx], 2*(childIdx+1)) <= |children[childrenIdx].strings|;
        BoundaryLe(children[childrenIdx], 2*childIdx, 2*(childIdx+1));
      }
      if (2*(parentIdx as int + 1) <= |parent.starts|) {
        LemmaStartEndIndices(parent, 2*parentIdx as int + 1);
        assert Boundary(parent, 2*(parentIdx+1)) <= |parent.strings|;
        BoundaryLe(parent, 2*parentIdx, 2*(parentIdx+1));
      }
      LemmaIArrayKeysLt(parent, children[childrenIdx], childrenIdx as int, parentIdx as int, childIdx as int, pivots, startsArray, startsIdx, stringsArray, stringsIdx);

      if (2*(parentIdx+1) as int < |parent.starts|) {
        KeysStrictlySortedImplLt(parent, parentIdx as int, parentIdx as int + 1);
        assert lt(Entry(parent, 2*parentIdx as int), Entry(parent, 2*(parentIdx as int + 1)));
      }
      if (2*(childIdx+1) as int < |children[childrenIdx].starts|) {
        KeysStrictlySortedImplLt(children[childrenIdx], childIdx as int, childIdx as int + 1);
        assert lt(Entry(children[childrenIdx], 2*childIdx as int), Entry(children[childrenIdx], 2*(childIdx as int + 1)));
      }
      PivotLeFirstChildOfNextBucket(childrenIdx, children, pivots);
      CurChildLtPivot(childrenIdx, childIdx as int, children, pivots);
      if childrenIdx+1 < |pivots| {
        IsStrictlySortedImpliesLt(pivots, childrenIdx, childrenIdx+1);
      }

      if (2*parentIdx == |parent.starts| as uint64) {
        if (2*childIdx == |children[childrenIdx].starts| as uint64) {
          LemmaAddMessagesToBucketsAugment(pivots, parent, children, childrenIdx as int, childIdx as int, parentIdx as int, res, res + [SSTable(startsArray[..startsIdx], stringsArray[..stringsIdx])], startsArray, stringsArray, startsIdx, stringsIdx);

          res := res + [SSTable(startsArray[..startsIdx], stringsArray[..stringsIdx])];

          startsIdx := 0;
          stringsIdx := 0;

          childIdx := 0;
          childrenIdx := childrenIdx + 1;

          assert childrenIdx < |children| ==> 2*parentIdx as int < |parent.starts| ==> forall key | key in IPrefix(children[childrenIdx], childIdx as int) :: lt(key, Entry(parent, 2*parentIdx as int));

          if (childrenIdx < |children| && 2*childIdx as int < |children[childrenIdx].starts|) {
            //assert SSTKeyMapsToValueAt(I(children[childrenIdx]), children[childrenIdx], 0);
            assert lte(pivots[childrenIdx-1], Entry(children[childrenIdx], 2*childIdx as int));
            assert forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, pivots[childrenIdx-1]);
            assert forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, Entry(children[childrenIdx], 2*childIdx as int));
          }
          assert childrenIdx < |children| - 1 ==> forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, pivots[childrenIdx-1]);
          assert childrenIdx < |children| - 1 ==> lt(pivots[childrenIdx-1], pivots[childrenIdx]);
          assert childrenIdx < |children| - 1 ==> forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, pivots[childrenIdx]);

          LemmaWFEmptyArrays(startsArray, stringsArray);
          if childrenIdx < |children| { EmptyAddMessagesToBucketWhenAllKeysInParentAreLt(pivots, childrenIdx - 1, IPrefix(parent, parentIdx as int)); }
          assert childrenIdx < |children| ==>
              IArrays(startsArray, startsIdx, stringsArray, stringsIdx)
           == map[]
           == BT.AddMessagesToBucket(pivots, childrenIdx, IPrefix(children[childrenIdx], childIdx as int), IPrefix(parent, parentIdx as int));
        } else {
          // TODO possible optimization: if childIdx is 0, then we can just use the existing childBucket with no changes

          startsIdx, stringsIdx := WriteKeyValue(startsArray, stringsArray, startsIdx, stringsIdx, children[childrenIdx], 2*childIdx);

          LemmaFlushAddChildKey(pivots, childrenIdx, oldIArray, IArrays(startsArray, startsIdx, stringsArray, stringsIdx), parent, children[childrenIdx], parentIdx as int, childIdx as int);

          childIdx := childIdx + 1; 

          assert childrenIdx < |children| ==> 2*parentIdx as int < |parent.starts| ==> forall key | key in IPrefix(children[childrenIdx], childIdx as int) :: lt(key, Entry(parent, 2*parentIdx as int));
          assert childrenIdx < |children| ==> 2*childIdx as int < |children[childrenIdx].starts| ==> forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, Entry(children[childrenIdx], 2*childIdx as int));
          assert childrenIdx < |children| - 1 ==> forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, pivots[childrenIdx]);

          assert childrenIdx < |children| ==>
              IArrays(startsArray, startsIdx, stringsArray, stringsIdx)
           == BT.AddMessagesToBucket(pivots, childrenIdx, IPrefix(children[childrenIdx], childIdx as int), IPrefix(parent, parentIdx as int));
        }
      } else {
        if (2*childIdx == |children[childrenIdx].starts| as uint64) {
          if (childrenIdx == |children| - 1) {
            startsIdx, stringsIdx := WriteKeyValue(startsArray, stringsArray, startsIdx, stringsIdx, parent, 2*parentIdx);

            LemmaFlushAddParentKey(pivots, childrenIdx, oldIArray, IArrays(startsArray, startsIdx, stringsArray, stringsIdx), parent, children[childrenIdx], parentIdx as int, childIdx as int);

            parentIdx := parentIdx + 1;

            assert childrenIdx < |children| ==> 2*parentIdx as int < |parent.starts| ==> forall key | key in IPrefix(children[childrenIdx], childIdx as int) :: lt(key, Entry(parent, 2*parentIdx as int));
            assert childrenIdx < |children| ==> 2*childIdx as int < |children[childrenIdx].starts| ==> forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, Entry(children[childrenIdx], 2*childIdx as int));
            assert childrenIdx < |children| - 1 ==> forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, pivots[childrenIdx]);
            assert childrenIdx < |children| ==>
                IArrays(startsArray, startsIdx, stringsArray, stringsIdx)
             == BT.AddMessagesToBucket(pivots, childrenIdx, IPrefix(children[childrenIdx], childIdx as int), IPrefix(parent, parentIdx as int));
          } else {
            var c := Cmp(pivots[childrenIdx], parent, 2*parentIdx);
            if (c == 1) {
              startsIdx, stringsIdx := WriteKeyValue(startsArray, stringsArray, startsIdx, stringsIdx, parent, 2*parentIdx);

              LemmaFlushAddParentKey(pivots, childrenIdx, oldIArray, IArrays(startsArray, startsIdx, stringsArray, stringsIdx), parent, children[childrenIdx], parentIdx as int, childIdx as int);

              parentIdx := parentIdx + 1;
              assert childrenIdx < |children| ==> 2*parentIdx as int < |parent.starts| ==> forall key | key in IPrefix(children[childrenIdx], childIdx as int) :: lt(key, Entry(parent, 2*parentIdx as int));
              assert childrenIdx < |children| ==> 2*childIdx as int < |children[childrenIdx].starts| ==> forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, Entry(children[childrenIdx], 2*childIdx as int));
              assert childrenIdx < |children| - 1 ==> forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, pivots[childrenIdx]);
              assert childrenIdx < |children| ==>
                  IArrays(startsArray, startsIdx, stringsArray, stringsIdx)
               == BT.AddMessagesToBucket(pivots, childrenIdx, IPrefix(children[childrenIdx], childIdx as int), IPrefix(parent, parentIdx as int));
            } else {
              LemmaAddMessagesToBucketsAugment(pivots, parent, children, childrenIdx as int, childIdx as int, parentIdx as int, res, res + [SSTable(startsArray[..startsIdx], stringsArray[..stringsIdx])], startsArray, stringsArray, startsIdx, stringsIdx);

              res := res + [SSTable(startsArray[..startsIdx], stringsArray[..stringsIdx])];

              startsIdx := 0;
              stringsIdx := 0;
              childIdx := 0;
              childrenIdx := childrenIdx + 1;

              assert childrenIdx < |children| ==> 2*parentIdx as int < |parent.starts| ==> forall key | key in IPrefix(children[childrenIdx], childIdx as int) :: lt(key, Entry(parent, 2*parentIdx as int));
              if (childrenIdx < |children| && 2*childIdx as int < |children[childrenIdx].starts|) {
                //assert SSTKeyMapsToValueAt(I(children[childrenIdx]), children[childrenIdx], 0);
                assert lte(pivots[childrenIdx-1], Entry(children[childrenIdx], 2*childIdx as int));
                assert forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, pivots[childrenIdx-1]);
                assert forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, Entry(children[childrenIdx], 2*childIdx as int));
              }

              assert childrenIdx < |children| - 1 ==> forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, pivots[childrenIdx-1]);
              assert childrenIdx < |children| - 1 ==> lt(pivots[childrenIdx-1], pivots[childrenIdx]);
              assert childrenIdx < |children| - 1 ==> forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, pivots[childrenIdx]);

              LemmaWFEmptyArrays(startsArray, stringsArray);
              if childrenIdx < |children| { EmptyAddMessagesToBucketWhenAllKeysInParentAreLt(pivots, childrenIdx - 1, IPrefix(parent, parentIdx as int)); }
              assert childrenIdx < |children| ==>
                  IArrays(startsArray, startsIdx, stringsArray, stringsIdx)
               == map[]
               == BT.AddMessagesToBucket(pivots, childrenIdx, IPrefix(children[childrenIdx], childIdx as int), IPrefix(parent, parentIdx as int));
            }
          }
        } else {
          var c := Cmp2(parent, 2*parentIdx as uint64, children[childrenIdx], 2*childIdx as uint64);
          if (c == 0) {
            startsIdx, stringsIdx := WriteKeyValue(startsArray, stringsArray, startsIdx, stringsIdx, parent, 2*parentIdx);

            LemmaFlushAddParentAndChildKey(pivots, childrenIdx, oldIArray, IArrays(startsArray, startsIdx, stringsArray, stringsIdx), parent, children[childrenIdx], parentIdx as int, childIdx as int);

            childIdx := childIdx + 1;
            parentIdx := parentIdx + 1;

            assert Entry(parent, 2*(parentIdx as int-1)) == Entry(children[childrenIdx], 2*(childIdx as int - 1));
            assert childrenIdx < |children| - 1 ==> lt(Entry(children[childrenIdx], 2*(childIdx as int - 1)), pivots[childrenIdx]);
            assert childrenIdx < |children| ==> 2*parentIdx as int < |parent.starts| ==> forall key | key in IPrefix(children[childrenIdx], childIdx as int) :: lt(key, Entry(parent, 2*parentIdx as int));
            assert childrenIdx < |children| ==> 2*childIdx as int < |children[childrenIdx].starts| ==> forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, Entry(children[childrenIdx], 2*childIdx as int));
            assert childrenIdx < |children| - 1 ==> forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, pivots[childrenIdx]);
            assert childrenIdx < |children| ==>
                IArrays(startsArray, startsIdx, stringsArray, stringsIdx)
             == BT.AddMessagesToBucket(pivots, childrenIdx, IPrefix(children[childrenIdx], childIdx as int), IPrefix(parent, parentIdx as int));
          } else if (c == -1) {
            startsIdx, stringsIdx := WriteKeyValue(startsArray, stringsArray, startsIdx, stringsIdx, parent, 2*parentIdx);

            LemmaFlushAddParentKey(pivots, childrenIdx, oldIArray, IArrays(startsArray, startsIdx, stringsArray, stringsIdx), parent, children[childrenIdx], parentIdx as int, childIdx as int);

            parentIdx := parentIdx + 1;

            assert lt(Entry(parent, 2*(parentIdx as int-1)), Entry(children[childrenIdx], 2*(childIdx as int)));
            assert childrenIdx < |children| - 1 ==> lt(Entry(children[childrenIdx], 2*(childIdx as int)), pivots[childrenIdx]);

            assert childrenIdx < |children| ==> 2*parentIdx as int < |parent.starts| ==> forall key | key in IPrefix(children[childrenIdx], childIdx as int) :: lt(key, Entry(parent, 2*parentIdx as int));
            assert childrenIdx < |children| ==> 2*childIdx as int < |children[childrenIdx].starts| ==> forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, Entry(children[childrenIdx], 2*childIdx as int));
            assert childrenIdx < |children| - 1 ==> forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, pivots[childrenIdx]);
            assert childrenIdx < |children| ==>
                IArrays(startsArray, startsIdx, stringsArray, stringsIdx)
             == BT.AddMessagesToBucket(pivots, childrenIdx, IPrefix(children[childrenIdx], childIdx as int), IPrefix(parent, parentIdx as int));
          } else if (c == 1) {
            startsIdx, stringsIdx := WriteKeyValue(startsArray, stringsArray, startsIdx, stringsIdx, children[childrenIdx], 2*childIdx);

            LemmaFlushAddChildKey(pivots, childrenIdx, oldIArray, IArrays(startsArray, startsIdx, stringsArray, stringsIdx), parent, children[childrenIdx], parentIdx as int, childIdx as int);

            childIdx := childIdx + 1; 

            assert childrenIdx < |children| ==> 2*parentIdx as int < |parent.starts| ==> forall key | key in IPrefix(children[childrenIdx], childIdx as int) :: lt(key, Entry(parent, 2*parentIdx as int));
            assert childrenIdx < |children| ==> 2*childIdx as int < |children[childrenIdx].starts| ==> forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, Entry(children[childrenIdx], 2*childIdx as int));
            assert childrenIdx < |children| - 1 ==> forall key | key in IPrefix(parent, parentIdx as int) :: lt(key, pivots[childrenIdx]);
            assert childrenIdx < |children| ==>
                IArrays(startsArray, startsIdx, stringsArray, stringsIdx)
             == BT.AddMessagesToBucket(pivots, childrenIdx, IPrefix(children[childrenIdx], childIdx as int), IPrefix(parent, parentIdx as int));
          }
        }
      }
    }
  }

  method Insert(sst: SSTable, key: Key, msg: Message)
  returns (res : SSTable)
  requires WFSSTableMap(sst)
  requires |sst.strings| < 0x800_0000_0000_0000
  requires |sst.starts| < 0x800_0000_0000_0000
  requires |key| < 0x400_0000_0000_0000
  requires msg.Define?
  requires |msg.value| < 0x400_0000_0000_0000
  ensures WFSSTableMap(res)
  ensures I(res) == I(sst)[key := msg]
  {
    Uint64Order.reveal_IsSorted();
    reveal_KeysStrictlySorted();
    var sst1 := SSTable([0, |key| as uint64], key + msg.value);
    var fl := DoFlush(sst1, [sst], []);
    res := fl[0];

    assert Entry(sst1, 0) == key;
    assert SSTKeyMapsToValueAt(I(sst1), sst1, 0);
    assert key in I(sst1);

    assert I(res) == BT.AddMessagesToBucket([], 0, I(sst), I(sst1));

    ghost var a := I(sst)[key := msg];
    ghost var b := BT.AddMessagesToBucket([], 0, I(sst), I(sst1));
    forall k | k in a
    ensures k in b
    ensures a[k] == b[k]
    {
      if (k == key) {
        //assert k in (I(sst1).Keys + I(sst).Keys);
        //assert P.Route([], k) == 0;
        //assert ValueMessage.Merge(BT.BucketLookup(I(sst1), k), BT.BucketLookup(I(sst), k)) != IdentityMessage();
      } else {
        if (k in I(sst1)) {
          ghost var i :| 0 <= 2*i < |sst1.starts| && Entry(sst1, 2*i) == k;
          assert false;
        }
        assert BT.BucketLookup(I(sst1), k) == IdentityMessage();
        assert k in I(sst);
        ghost var i :| 0 <= 2*i < |sst.starts| && Entry(sst, 2*i) == k;
        assert SSTKeyMapsToValueAt(I(sst), sst, i);

        /*assert BT.BucketLookup(I(sst), k) != IdentityMessage();
        assert ValueMessage.Merge(BT.BucketLookup(I(sst1), k), BT.BucketLookup(I(sst), k))
            == BT.BucketLookup(I(sst), k);

        assert k in (I(sst1).Keys + I(sst).Keys);
        assert P.Route([], k) == 0;
        assert ValueMessage.Merge(BT.BucketLookup(I(sst1), k), BT.BucketLookup(I(sst), k)) != IdentityMessage();*/
      }
    }
    forall k | k in b
    ensures k in a
    {
    }

    /*
    var lo := 0;
    var hi := Size(sst);
    while lo < hi
    invariant lo <= hi
    invariant forall i | 0 <= i < lo :: lt(Entry(sst, 2*i), key)
    invariant forall i | hi <= i <= Size(sst) :: lt(key, Entry(sst, 2*i))
    decreases hi - lo
    {
      var mid := (lo + hi) / 2;
      
      var c := Cmp(key, sst, 2*mid);
      if (c == -1) {
        lo = mid + 1;
      }
      else if (c == 1) {
        hi = mid;
      }
      else {
        res := 
      }
    }
    */
  }

  function addToStarts(starts: seq<uint64>, offset: uint64) : (res : seq<uint64>)
  requires forall i | 0 <= i < |starts| :: starts[i] as int + offset as int < 0x1_0000_0000_0000_0000
  ensures |res| == |starts|
  ensures forall i | 0 <= i < |res| :: res[i] == starts[i] + offset
  {
    if |starts| == 0 then [] else addToStarts(DropLast(starts), offset) + [Last(starts) + offset]
  }

  method CopySeqIntoArrayAdding(s: seq<uint64>, ar: array<uint64>, dstIdx: uint64, offset: uint64)
  requires forall i | 0 <= i < |s| :: s[i] as int + offset as int < 0x1_0000_0000_0000_0000
  requires 0 <= dstIdx
  requires dstIdx as int + |s| <= ar.Length
  requires |s| < 0x1_0000_0000_0000_0000
  requires ar.Length < 0x1_0000_0000_0000_0000
  modifies ar
  ensures old(ar[..dstIdx]) == ar[..dstIdx]
  ensures ar[dstIdx .. dstIdx as int + |s|] == addToStarts(s, offset)
  {
    var i: uint64 := 0;
    while i < |s| as uint64
    invariant 0 <= i as int <= |s|
    invariant ar[dstIdx .. dstIdx as int + i as int] == addToStarts(s[..i], offset)
    invariant old(ar[..dstIdx]) == ar[..dstIdx]
    {
      ar[dstIdx + i] := s[i] + offset; 
      i := i + 1;
    }
  }

  function subFromStarts(starts: seq<uint64>, offset: uint64) : (res: seq<uint64>)
  requires forall i | 0 <= i < |starts| :: offset <= starts[i]
  ensures |res| == |starts|
  ensures forall i | 0 <= i < |res| :: res[i] == starts[i] - offset
  {
    if |starts| == 0 then [] else subFromStarts(DropLast(starts), offset) + [Last(starts) - offset]
  }

  method CopySeqIntoArraySubtracting(s: seq<uint64>, ar: array<uint64>, dstIdx: uint64, offset: uint64)
  requires forall i | 0 <= i < |s| :: offset <= s[i]
  requires 0 <= dstIdx
  requires dstIdx as int + |s| <= ar.Length
  requires |s| < 0x1_0000_0000_0000_0000
  requires ar.Length < 0x1_0000_0000_0000_0000
  modifies ar
  ensures old(ar[..dstIdx]) == ar[..dstIdx]
  ensures ar[dstIdx .. dstIdx as int + |s|] == subFromStarts(s, offset)
  {
    var i: uint64 := 0;
    while i < |s| as uint64
    invariant 0 <= i as int <= |s|
    invariant ar[dstIdx .. dstIdx as int + i as int] == subFromStarts(s[..i], offset)
    invariant old(ar[..dstIdx]) == ar[..dstIdx]
    {
      ar[dstIdx + i] := s[i] - offset; 
      i := i + 1;
    }
  }

  lemma subFromStartsSorted(starts: seq<uint64>, offset: uint64)
  requires subFromStarts.requires(starts, offset)
  requires Uint64Order.IsSorted(starts)
  ensures Uint64Order.IsSorted(subFromStarts(starts, offset))
  {
    Uint64Order.reveal_IsSorted();
  }

  lemma startsAppendAddToStartsSorted(
      starts: seq<uint64>,
      starts2: seq<uint64>,
      offset: uint64)
  requires addToStarts.requires(starts2, offset)
  requires Uint64Order.IsSorted(starts)
  requires Uint64Order.IsSorted(starts2)
  requires |starts| > 0 ==> Last(starts) <= offset
  ensures Uint64Order.IsSorted(starts + addToStarts(starts2, offset))
  {
    //var run := starts + addToStarts(starts2, offset);
    Uint64Order.reveal_IsSorted();
    //forall i, j | 0 <= i <= j < |run| ensures run[i] <= run[j]
    //{
    //}
  }

  lemma lemmaJoinStartsInBounds(sst: SSTable, offset: uint64)
  requires WFSSTable(sst)
  requires |sst.strings| < 0x10_0000_0000_0000
  requires offset < 0x10_0000_0000_0000 * (0x100 - 1)
  ensures forall i | 0 <= i < |sst.starts| :: sst.starts[i] as int + offset as int < 0x1_0000_0000_0000_0000
  {
    Uint64Order.reveal_IsSorted();
  }

  function join(ssts: seq<SSTable>) : (sst : SSTable)
  requires |ssts| < 0x100
  requires forall i | 0 <= i < |ssts| :: WFSSTable(ssts[i])
  requires forall i | 0 <= i < |ssts| :: |ssts[i].strings| < 0x10_0000_0000_0000
  requires forall i | 0 <= i < |ssts| :: |ssts[i].starts| < 0x10_0000_0000_0000
  ensures |sst.strings| <= |ssts| * 0x10_0000_0000_0000
  ensures |sst.starts| <= |ssts| * 0x10_0000_0000_0000
  ensures WFSSTable(sst)
  {
    if |ssts| == 0 then (
      reveal_Empty();
      Empty()
    ) else (
      var pref := join(DropLast(ssts));
      var last := Last(ssts);

      lemmaJoinStartsInBounds(last, |pref.strings| as uint64);
      startsAppendAddToStartsSorted(pref.starts, last.starts, |pref.strings| as uint64);

      var sst := SSTable(
        pref.starts + addToStarts(last.starts, |pref.strings| as uint64),
        pref.strings + last.strings
      );

      assert Uint64Order.IsSorted(sst.starts);
      assert (|sst.starts| > 0 ==> (
        && sst.starts[0] == 0
        && 0 <= Last(sst.starts) as int <= |sst.strings|
      ));
      assert (|sst.starts| == 0 ==> |sst.strings| == 0);

      sst
    ) 
  }

  /*predicate AllKeysLt(sst1: SSTable, sst2: SSTable)
  requires WFSSTableMap(sst1)
  requires WFSSTableMap(sst2)
  {
    forall key1, key2 | key1 in I(sst1) && key2 in I(sst2) :: lt(key1, key2)
  }*/

  lemma join2Preserves(sst1: SSTable, sst2: SSTable, sst: SSTable, i: int)
  requires WFSSTableMap(sst1)
  requires WFSSTableMap(sst2)
  requires WFSSTable(sst)
  requires sst.strings == sst1.strings + sst2.strings
  requires addToStarts.requires(sst2.starts, |sst1.strings| as uint64)
  requires sst.starts == sst1.starts + addToStarts(sst2.starts, |sst1.strings| as uint64)
  requires 0 <= 2*i < |sst.starts|
  ensures 2*i < |sst1.starts| ==> Entry(sst, 2*i) == Entry(sst1, 2*i)
  ensures 2*i < |sst1.starts| ==> Entry(sst, 2*i + 1) == Entry(sst1, 2*i + 1)
  ensures 2*i >= |sst1.starts| ==> Entry(sst, 2*i) == Entry(sst2, 2*(i - |sst1.starts|/2))
  ensures 2*i >= |sst1.starts| ==> Entry(sst, 2*i + 1) == Entry(sst2, 2*(i - |sst1.starts|/2) + 1)
  {
    LemmaStartEndIndices(sst, 2*i);
    LemmaStartEndIndices(sst, 2*i+1);
    if (2*i < |sst1.starts|) {
      LemmaStartEndIndices(sst1, 2*i);
      LemmaStartEndIndices(sst1, 2*i+1);
    } else {
      LemmaStartEndIndices(sst2, 2*i - |sst1.starts|);
      LemmaStartEndIndices(sst2, 2*i+1 - |sst1.starts|);

      assert Entry(sst, 2*i)
          == sst.strings[Start(sst, 2*i as uint64) .. End(sst, 2*i as uint64)]
          == sst2.strings[Start(sst2, 2*(i - |sst1.starts|/2) as uint64) .. End(sst2, 2*(i - |sst1.starts|/2) as uint64)]
          == Entry(sst2, 2*(i - |sst1.starts|/2));
      assert Entry(sst, 2*i+1)
          == sst.strings[Start(sst, 2*i as uint64 + 1) .. End(sst, 2*i as uint64 + 1)]
          == sst2.strings[Start(sst2, 2*(i - |sst1.starts|/2) as uint64 + 1) .. End(sst2, 2*(i - |sst1.starts|/2) as uint64 + 1)]
          == Entry(sst2, 2*(i - |sst1.starts|/2) + 1);
    }
  }

  lemma join2IsJoinBuckets(sst1: SSTable, sst2: SSTable, sst: SSTable)
  requires WFSSTableMap(sst1)
  requires WFSSTableMap(sst2)
  requires WFSSTable(sst)
  requires sst.strings == sst1.strings + sst2.strings
  requires addToStarts.requires(sst2.starts, |sst1.strings| as uint64)
  requires sst.starts == sst1.starts + addToStarts(sst2.starts, |sst1.strings| as uint64)
  requires forall key1, key2 | key1 in I(sst1) && key2 in I(sst2) :: lt(key1, key2)
  ensures WFSSTableMap(sst)
  ensures I(sst1) !! I(sst2)
  ensures I(sst) == MapUnion(I(sst1), I(sst2))
  {
    reveal_KeysStrictlySorted();
    forall i, j | 0 <= 2*i < 2*j < |sst.starts|
    ensures lt(Entry(sst, 2*i), Entry(sst, 2*j))
    {
      join2Preserves(sst1, sst2, sst, i);
      join2Preserves(sst1, sst2, sst, j);
      if (2*i < |sst1.starts|) {
        assert SSTKeyMapsToValueAt(I(sst1), sst1, i);
      }
      if (2*j >= |sst1.starts|) {
        assert SSTKeyMapsToValueAt(I(sst2), sst2, j - |sst1.starts|/2);
      }
    }

    forall key | key in (I(sst1).Keys * I(sst2).Keys) ensures false { }
    assert I(sst1).Keys * I(sst2).Keys == {};

    forall key | key in I(sst1)
    ensures key in I(sst)
    ensures I(sst)[key] == I(sst1)[key]
    {
      var i :| 0 <= 2*i < |sst1.starts| && Entry(sst1, 2*i) == key;
      join2Preserves(sst1, sst2, sst, i);
      assert SSTKeyMapsToValueAt(I(sst), sst, i);
      assert SSTKeyMapsToValueAt(I(sst1), sst1, i);
    }
    forall key | key in I(sst2)
    ensures key in I(sst)
    ensures I(sst)[key] == I(sst2)[key]
    {
      var i :| 0 <= 2*i < |sst2.starts| && Entry(sst2, 2*i) == key;
      join2Preserves(sst1, sst2, sst, i + |sst1.starts|/2);
      assert SSTKeyMapsToValueAt(I(sst), sst, i + |sst1.starts|/2);
      assert SSTKeyMapsToValueAt(I(sst2), sst2, i);
    }
    forall key | key in I(sst) ensures (key in I(sst1) || key in I(sst2))
    {
      var i :| 0 <= 2*i < |sst.starts| && Entry(sst, 2*i) == key;
      join2Preserves(sst1, sst2, sst, i);
      if (2*i < |sst1.starts|) {
        assert SSTKeyMapsToValueAt(I(sst1), sst1, i);
      }
      if (2*i >= |sst1.starts|) {
        assert SSTKeyMapsToValueAt(I(sst2), sst2, i - |sst1.starts|/2);
      }
    }

    IsMapUnion(I(sst1), I(sst2), I(sst));
  }

  lemma joinDropLastLt(ssts: seq<SSTable>, sst1: SSTable, sst2: SSTable)
  requires join.requires(ssts)
  requires forall i | 0 <= i < |ssts| :: WFSSTableMap(ssts[i])
  requires forall i, j, key1, key2 | 0 <= i < j < |ssts| && key1 in I(ssts[i]) && key2 in I(ssts[j]) :: lt(key1, key2)
  requires |ssts| > 0
  requires WFSSTableMap(sst1)
  requires WFSSTableMap(sst2)
  requires I(sst1) == BT.JoinBuckets(ISeq(DropLast(ssts)))
  requires sst2 == Last(ssts)
  ensures forall key1, key2 | key1 in I(sst1) && key2 in I(sst2) :: lt(key1, key2)

  lemma joinIsJoinBuckets(ssts: seq<SSTable>)
  requires join.requires(ssts)
  requires forall i | 0 <= i < |ssts| :: WFSSTableMap(ssts[i])
  requires forall i, j, key1, key2 | 0 <= i < j < |ssts| && key1 in I(ssts[i]) && key2 in I(ssts[j]) :: lt(key1, key2)
  //requires forall i, j | 0 <= i < j < |ssts| :: AllKeysLt(ssts[i], ssts[j])
  ensures WFSSTableMap(join(ssts))
  ensures I(join(ssts)) == BT.JoinBuckets(ISeq(ssts))
  {
    reveal_KeysStrictlySorted();
    if (|ssts| == 0) {
    } else {
      joinIsJoinBuckets(DropLast(ssts));
      joinDropLastLt(ssts, join(DropLast(ssts)), Last(ssts));
      join2IsJoinBuckets(join(DropLast(ssts)), Last(ssts), join(ssts));
    }
  }

  function startsSum(ssts: seq<SSTable>) : int
  {
    if |ssts| == 0 then 0 else startsSum(DropLast(ssts)) + |Last(ssts).starts|
  }

  function stringsSum(ssts: seq<SSTable>) : int
  {
    if |ssts| == 0 then 0 else stringsSum(DropLast(ssts)) + |Last(ssts).strings|
  }

  lemma lemmaStartsStringsSumPrefixLe(ssts: seq<SSTable>, i: int)
  requires 0 <= i <= |ssts|
  ensures startsSum(ssts[..i]) <= startsSum(ssts)
  ensures stringsSum(ssts[..i]) <= stringsSum(ssts)
  {
    if i == |ssts| {
      assert ssts[..i] == ssts;
    } else {
      assert DropLast(ssts)[..i] == ssts[..i];
      lemmaStartsStringsSumPrefixLe(DropLast(ssts), i);
    }
  }

  method {:fuel BT.JoinBuckets,0} DoJoin(ssts: seq<SSTable>)
  returns (sst: SSTable)
  requires join.requires(ssts)
  requires forall i | 0 <= i < |ssts| :: WFSSTableMap(ssts[i])
  requires forall i, j, key1, key2 | 0 <= i < j < |ssts| && key1 in I(ssts[i]) && key2 in I(ssts[j]) :: lt(key1, key2)
  ensures WFSSTableMap(sst)
  ensures I(sst) == BT.JoinBuckets(ISeq(ssts))
  {
    var startsLen: uint64 := 0;
    var stringsLen: uint64 := 0;
    var i: uint64 := 0;
    while i < |ssts| as uint64
    invariant 0 <= i as int <= |ssts|
    invariant startsLen as int == startsSum(ssts[..i])
    invariant stringsLen as int == stringsSum(ssts[..i])
    invariant startsLen as int <= i as int * 0x10_0000_0000_0000
    invariant stringsLen as int <= i as int * 0x10_0000_0000_0000
    {
      assert DropLast(ssts[..i+1]) == ssts[..i];
      assert Last(ssts[..i+1]) == ssts[i];

      startsLen := startsLen + |ssts[i].starts| as uint64;
      stringsLen := stringsLen + |ssts[i].strings| as uint64;
      i := i + 1;
    }

    assert ssts[..i] == ssts;

    var starts := new uint64[startsLen];
    var strings := new byte[stringsLen];
    var startsIdx: uint64 := 0;
    var stringsIdx: uint64 := 0;
    var j: uint64 := 0;
    while j < |ssts| as uint64
    invariant 0 <= j as int <= |ssts|
    invariant 0 <= startsIdx as int <= starts.Length
    invariant 0 <= stringsIdx as int <= strings.Length
    invariant startsIdx as int == startsSum(ssts[..j])
    invariant stringsIdx as int == stringsSum(ssts[..j])
    invariant SSTable(starts[..startsIdx], strings[..stringsIdx]) == join(ssts[..j])
    {
      ghost var pref := join(ssts[..j]);

      assert DropLast(ssts[..j+1]) == ssts[..j];
      assert Last(ssts[..j+1]) == ssts[j];
      assert startsIdx as int + |ssts[j].starts| == startsSum(ssts[..j+1]);
      assert stringsIdx as int + |ssts[j].strings| == stringsSum(ssts[..j+1]);
      lemmaStartsStringsSumPrefixLe(ssts, j as int + 1);
      lemmaJoinStartsInBounds(ssts[j], stringsIdx);

      Native.Arrays.CopySeqIntoArray(ssts[j].strings, 0, strings, stringsIdx, |ssts[j].strings| as uint64);
      CopySeqIntoArrayAdding(ssts[j].starts, starts, startsIdx as uint64, stringsIdx as uint64);

      assert join(ssts[..j+1])
          == SSTable(pref.starts + addToStarts(ssts[j].starts, |pref.strings| as uint64), pref.strings + ssts[j].strings)
          == SSTable(starts[..startsIdx] + addToStarts(ssts[j].starts, |pref.strings| as uint64), strings[..stringsIdx] + ssts[j].strings)
          == SSTable(starts[..startsIdx as int + |ssts[j].starts|], strings[..stringsIdx as int + |ssts[j].strings|]);

      stringsIdx := stringsIdx + |ssts[j].strings| as uint64;
      startsIdx := startsIdx + |ssts[j].starts| as uint64;
      j := j + 1;
    }

    sst := SSTable(starts[..], strings[..]);

    assert sst == join(ssts);
    joinIsJoinBuckets(ssts); // lemma
  }

  function method EmptySeq(n: int) : (s : seq<SSTable>)
  requires n >= 0
  ensures |s| == n
  ensures forall i | 0 <= i < n :: WFSSTableMap(s[i])
  ensures forall i | 0 <= i < n :: s[i] == Empty()
  {
    if n == 0 then [] else EmptySeq(n-1) + [Empty()]
  }

  lemma LemmaSplitBucketOnPivotsEqAddMessagesToBuckets(bucket: map<Key, Message>, pivots: seq<Key>, emp: seq<map<Key, Message>>)
  requires P.WFPivots(pivots)
  requires |emp| == |pivots| + 1
  ensures forall i | 0 <= i < |emp| :: emp[i] == map[]
  ensures BT.SplitBucketOnPivots(pivots, bucket) == BT.AddMessagesToBuckets(pivots, |emp|, emp, bucket)

  method SplitOnPivots(sst: SSTable, pivots: seq<Key>)
  returns (ssts : seq<SSTable>)
  requires WFSSTableMap(sst)
  requires P.WFPivots(pivots)
  requires |sst.strings| < 0x800_0000_0000_0000
  requires |sst.starts| < 0x800_0000_0000_0000
  ensures forall i | 0 <= i < |ssts| :: WFSSTableMap(ssts[i])
  ensures ISeq(ssts) == BT.SplitBucketOnPivots(pivots, I(sst))
  {
    reveal_Empty();
    ssts := DoFlush(sst, EmptySeq(|pivots| + 1), pivots);

    LemmaSplitBucketOnPivotsEqAddMessagesToBuckets(I(sst), pivots, ISeq(EmptySeq(|pivots| + 1)));
  }

  function method KeyAtIndex(sst: SSTable, i: int) : (key: Key)
  requires WFSSTableMap(sst)
  requires 0 <= i < Size(sst) as int
  ensures 2*i <= |sst.starts|
  ensures key == Entry(sst, 2*i)
  {
    Entry(sst, 2*i)
  }

  lemma Ireplace1with2(ssts: seq<SSTable>, sst1: SSTable, sst2: SSTable, slot: int)
  requires WFSSTableMap(sst1)
  requires WFSSTableMap(sst2)
  requires 0 <= slot < |ssts|
  requires forall i | 0 <= i < |ssts| :: WFSSTableMap(ssts[i])
  ensures forall i | 0 <= i < |replace1with2(ssts, sst1, sst2, slot)| :: WFSSTableMap(replace1with2(ssts, sst1, sst2, slot)[i])
  ensures ISeq(replace1with2(ssts, sst1, sst2, slot)) == replace1with2(ISeq(ssts), I(sst1), I(sst2), slot)
  {
    forall i | 0 <= i < |replace1with2(ssts, sst1, sst2, slot)|
    ensures WFSSTableMap(replace1with2(ssts, sst1, sst2, slot)[i])
    {
      if i < slot {
        assert replace1with2(ssts, sst1, sst2, slot)[i] == ssts[i];
      }
      if i == slot {
        assert replace1with2(ssts, sst1, sst2, slot)[i] == sst1;
      }
      if i == slot + 1 {
        assert replace1with2(ssts, sst1, sst2, slot)[i] == sst2;
      }
      if i > slot + 1 {
        assert replace1with2(ssts, sst1, sst2, slot)[i] == ssts[i-1];
      }
    }

    if slot == |ssts|-1 {
    } else {
      Ireplace1with2(DropLast(ssts), sst1, sst2, slot);
    }

    reveal_replace1with2();
  }

  lemma Islice(ssts: seq<SSTable>, a: int, b: int)
  requires 0 <= a <= b <= |ssts|
  requires forall i | 0 <= i < |ssts| :: WFSSTableMap(ssts[i])
  ensures forall i | 0 <= i < |ssts[a..b]| :: WFSSTableMap(ssts[a..b][i])
  ensures ISeq(ssts[a..b]) == ISeq(ssts)[a..b]
  {
    if b == |ssts| {
      if (a == b) {
      } else {
        Islice(DropLast(ssts), a, b - 1);
      }
    } else {
      Islice(DropLast(ssts), a, b);
    }
  }

  lemma Isuffix(ssts: seq<SSTable>, a: int)
  requires 0 <= a <= |ssts|
  requires forall i | 0 <= i < |ssts| :: WFSSTableMap(ssts[i])
  ensures forall i | 0 <= i < |ssts[a..]| :: WFSSTableMap(ssts[a..][i])
  ensures ISeq(ssts[a..]) == ISeq(ssts)[a..]
  {
    Islice(ssts, a, |ssts|);
  }

  method IsWFSSTableMap(sst: SSTable)
  returns (b: bool)
  ensures b == WFSSTableMap(sst)
  {
    var startsSorted := Uint64Order.ComputeIsSorted(sst.starts);
    if (!startsSorted) { return false; }

    if (!(
        && |sst.strings| < 0x1000_0000_0000_0000
        && |sst.starts| < 0x1000_0000_0000_0000
        && (|sst.starts| > 0 ==> (
          && sst.starts[0] == 0
          && 0 <= Last(sst.starts) as int <= |sst.strings|
        ))
        && (|sst.starts| == 0 ==> |sst.strings| == 0)
    )) { return false; }

    if |sst.starts| % 2 != 0 { return false; }

    reveal_KeysStrictlySorted();

    var k: uint64 := 2;
    ghost var m := 1;
    while k as int < |sst.starts|
    invariant k as int == m * 2
    invariant |sst.starts| > 0 ==> 0 <= k as int <= |sst.starts|
    invariant |sst.starts| > 0 ==> forall i, j :: 0 <= 2*i < 2*j < k as int ==> lt(Entry(sst, 2*i), Entry(sst, 2*j))
    {
      var c := Cmp2(sst, k-2, sst, k);
      if (c != -1) {
        assert !lt(Entry(sst, 2*(m-1)), Entry(sst, 2*m));
        return false;
      }
      k := k + 2;
      m := m + 1;

      forall i, j | 0 <= 2*i < 2*j < k as int
      ensures lt(Entry(sst, 2*i), Entry(sst, 2*j))
      {
        if (j == m - 1 as int) {
          assert lte(Entry(sst, 2*i), Entry(sst, 2*(m-2)));
          assert lte(Entry(sst, 2*(m-2)), Entry(sst, 2*(m-1)));
          assert lt(Entry(sst, 2*i), Entry(sst, 2*j));
        } else {
          assert 2*j < k as int - 2;
          assert lt(Entry(sst, 2*i), Entry(sst, 2*j));
        }
      }
    }

    return true;
  }

  method ComputeCutoffPoint(sst: SSTable, key: Key)
  returns (idx: uint64)
  requires WFSSTableMap(sst)
  ensures 0 <= 2*idx as int <= |sst.starts|
  ensures forall i | 0 <= 2*i < 2*idx as int :: lt(Entry(sst, 2*i), key)
  ensures forall i | 2*idx as int <= 2*i as int < |sst.starts| :: lte(key, Entry(sst, 2*i))
  {
    var lo: uint64 := 0;
    var hi: uint64 := (|sst.starts| as uint64) / 2;

    while lo < hi
    invariant 0 <= 2*lo as int <= |sst.starts|
    invariant 0 <= 2*hi as int <= |sst.starts|
    invariant forall i | 0 <= 2*i < 2*lo as int :: lt(Entry(sst, 2*i), key)
    invariant forall i | 2*hi as int <= 2*i < |sst.starts| :: lte(key, Entry(sst, 2*i))
    decreases hi as int - lo as int
    {
      reveal_KeysStrictlySorted();

      var mid: uint64 := (lo + hi) / 2;
      var c := Cmp(key, sst, 2*mid);
      if (c == 1) {
        lo := mid + 1;
      } else {
        hi := mid;
      }
    }

    idx := lo;
  }

  lemma leftPreserves(sst: SSTable, left: SSTable, idx: int, stringIdx: int, i: int)
  requires WFSSTableMap(sst)
  requires WFSSTable(left)
  requires 0 <= 2*idx <= |sst.starts|
  requires 0 <= stringIdx <= |sst.strings|
  requires stringIdx == (if 2*idx == |sst.starts| then |sst.strings| else sst.starts[2*idx] as int)
  requires left.starts == sst.starts[.. 2*idx]
  requires left.strings == sst.strings[.. stringIdx]
  requires 0 <= i < idx
  ensures Entry(sst, 2*i) == Entry(left, 2*i)
  ensures Entry(sst, 2*i + 1) == Entry(left, 2*i + 1)
  {
    LemmaStartEndIndices(sst, 2*i);
    LemmaStartEndIndices(sst, 2*i+1);
    LemmaStartEndIndices(left, 2*i);
    LemmaStartEndIndices(left, 2*i+1);
    //assert Entry(sst, 2*i)
    //    == sst.strings[Start(sst, 2*i as uint64)..End(sst, 2*i as uint64)]
    //    == left.strings[Start(sst, 2*i as uint64)..End(sst, 2*i as uint64)]
    //    == left.strings[Start(left, 2*i as uint64)..End(left, 2*i as uint64)]
    //    == Entry(left, 2*i);
  }

  method SplitLeft(sst: SSTable, pivot: Key)
  returns (left: SSTable)
  requires WFSSTableMap(sst)
  ensures WFSSTableMap(left)
  ensures I(left) == BT.SplitBucketLeft(I(sst), pivot)
  {
    Uint64Order.reveal_IsSorted();
    reveal_KeysStrictlySorted();

    var idx := ComputeCutoffPoint(sst, pivot);
    var stringIdx := (if 2*idx == |sst.starts| as uint64 then |sst.strings| as uint64 else sst.starts[2*idx]);
    left := SSTable(sst.starts[.. 2 * idx], sst.strings[.. stringIdx]);

    forall i, j | 0 <= 2*i < 2*j < |left.starts|
    ensures lt(Entry(left, 2*i), Entry(left, 2*j))
    {
      leftPreserves(sst, left, idx as int, stringIdx as int, i);
      leftPreserves(sst, left, idx as int, stringIdx as int, j);
    }

    ghost var a := BT.SplitBucketLeft(I(sst), pivot);
    ghost var b := I(left);

    forall key | key in a
    ensures key in b
    ensures a[key] == b[key]
    {
      var i :| 0 <= 2*i < |sst.starts| && Entry(sst, 2*i) == key;
      assert 2*i < |left.starts|;
      assert SSTKeyMapsToValueAt(I(left), left, i);
      assert SSTKeyMapsToValueAt(I(sst), sst, i);
      leftPreserves(sst, left, idx as int, stringIdx as int, i);
    }

    forall key | key in b
    ensures key in a
    {
      var i :| 0 <= 2*i < |left.starts| && Entry(left, 2*i) == key;
      leftPreserves(sst, left, idx as int, stringIdx as int, i);
      assert SSTKeyMapsToValueAt(I(sst), sst, i);
      //assert lt(Entry(sst, 2*i), pivot);
      //assert key in I(sst);
      //assert lt(key, pivot);
    }

    assert a == b;
  }

  lemma rightPreserves(sst: SSTable, right: SSTable, idx: int, stringIdx: int, i: int)
  requires WFSSTableMap(sst)
  requires WFSSTable(right)
  requires 0 <= 2*idx <= |sst.starts|
  requires 0 <= stringIdx <= |sst.strings|
  requires stringIdx == (if 2*idx == |sst.starts| then |sst.strings| else sst.starts[2*idx] as int)
  requires forall i | 2*idx <= i < |sst.starts| :: stringIdx <= sst.starts[i] as int
  requires right.starts == subFromStarts(sst.starts[2*idx ..], stringIdx as uint64);
  requires right.strings == sst.strings[stringIdx ..]
  requires 2*idx <= 2*i < |sst.starts|
  ensures Entry(sst, 2*i) == Entry(right, 2*i - 2*idx)
  ensures Entry(sst, 2*i + 1) == Entry(right, 2*i + 1 - 2*idx)
  {
    LemmaStartEndIndices(sst, 2*i);
    LemmaStartEndIndices(sst, 2*i+1);
    LemmaStartEndIndices(right, 2*i - 2*idx);
    LemmaStartEndIndices(right, 2*i+1 - 2*idx);
  }

  lemma LemmaSplitRight(sst: SSTable, pivot: Key, idx: uint64, stringIdx: uint64)
  requires WFSSTableMap(sst)
  requires 0 <= 2*idx as int <= |sst.starts|
  requires stringIdx == (if 2*idx == |sst.starts| as uint64 then |sst.strings| as uint64 else sst.starts[2*idx])
  ensures forall i | 0 <= i < |sst.starts[2*idx..]| :: stringIdx <= sst.starts[2*idx..][i]
  ensures Uint64Order.IsSorted(sst.starts[2*idx..])
  {
    Uint64Order.reveal_IsSorted();
  }

  method SplitRight(sst: SSTable, pivot: Key)
  returns (right: SSTable)
  requires WFSSTableMap(sst)
  ensures WFSSTableMap(right)
  ensures I(right) == BT.SplitBucketRight(I(sst), pivot)
  {
    //Uint64Order.reveal_IsSorted();
    reveal_KeysStrictlySorted();

    var idx: uint64 := ComputeCutoffPoint(sst, pivot);
    var stringIdx := (if 2*idx == |sst.starts| as uint64 then |sst.strings| as uint64 else sst.starts[2*idx]);

    LemmaSplitRight(sst, pivot, idx, stringIdx);

    var startsArray := new uint64[|sst.starts| as uint64 - 2*idx];
    CopySeqIntoArraySubtracting(sst.starts[2*idx..], startsArray, 0, stringIdx);

    right := SSTable(startsArray[..], sst.strings[stringIdx ..]);

    assert startsArray[..] == subFromStarts(sst.starts[2*idx..], stringIdx);
    subFromStartsSorted(sst.starts[2*idx..], stringIdx);
    forall i, j | 0 <= 2*i < 2*j < |right.starts|
    ensures lt(Entry(right, 2*i), Entry(right, 2*j))
    {
      rightPreserves(sst, right, idx as int, stringIdx as int, i + idx as int);
      rightPreserves(sst, right, idx as int, stringIdx as int, j + idx as int);
    }

    ghost var a := BT.SplitBucketRight(I(sst), pivot);
    ghost var b := I(right);

    forall key | key in a
    ensures key in b
    ensures a[key] == b[key]
    {
      var i :| 0 <= 2*i < |sst.starts| && Entry(sst, 2*i) == key;
      assert 0 <= 2*i - 2*idx as int < |right.starts|;
      assert SSTKeyMapsToValueAt(I(right), right, i - idx as int);
      assert SSTKeyMapsToValueAt(I(sst), sst, i);
      rightPreserves(sst, right, idx as int, stringIdx as int, i);
    }

    forall key | key in b
    ensures key in a
    {
      var i :| 0 <= 2*i < |right.starts| && Entry(right, 2*i) == key;
      rightPreserves(sst, right, idx as int, stringIdx as int, i + idx as int);
      assert SSTKeyMapsToValueAt(I(sst), sst, i + idx as int);
      //assert lt(Entry(sst, 2*i), pivot);
      //assert key in I(sst);
      //assert lt(key, pivot);
    }

    assert a == b;
  }

}
