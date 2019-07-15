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
}
