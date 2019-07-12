include "../lib/sequences.dfy"
include "../lib/maps.dfy"
include "../lib/total_order.dfy"
include "Message.dfy"
include "PivotBetreeSpec.dfy"
include "../lib/Marshalling/Native.s.dfy"

module SSTable {
  import opened ValueMessage
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

  predicate WFSSTableMap(sst: SSTable)
  {
    && WFSSTable(sst)
    && Even(|sst.starts|)
    && KeysStrictlySorted(sst)
  }

  function {:opaque} IPrefix(sst: SSTable, k: int) : (m : map<String, Message>)
  requires WFSSTableMap(sst)
  requires 2*k <= |sst.starts|
  ensures forall i | 0 <= i < k :: Entry(sst, 2*i) in m && m[Entry(sst, 2*i)] == Define(Entry(sst, 1 + 2*i));
  ensures forall key | key in m :: exists i :: 0 <= i < k && Entry(sst, 2*i) == key

  function {:opaque} I(sst: SSTable) : (m : map<String, Message>)
  requires WFSSTableMap(sst)
  ensures forall i | 0 <= 2*i < |sst.starts| :: Entry(sst, 2*i) in m && m[Entry(sst, 2*i)] == Define(Entry(sst, 1 + 2*i));
  ensures forall key | key in m :: exists i :: 0 <= 2*i < |sst.starts| && Entry(sst, 2*i) == key

  function ISeq(ssts: seq<SSTable>) : (res : seq<map<String, Message>>)
  requires forall i | 0 <= i < |ssts| :: WFSSTableMap(ssts[i])
  ensures |res| == |ssts|
  ensures forall i | 0 <= i < |ssts| :: I(ssts[i]) == res[i]

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

  method Cmp2(sst: SSTable, i: uint64, sst': SSTable, j: uint64) returns (c: int32)
  requires WFSSTable(sst)
  requires WFSSTable(sst')
  requires 0 <= i as int < |sst.starts|
  requires 0 <= j as int < |sst'.starts|
  ensures c == 0 || c == -1 || c == 1
  ensures c == 0 ==> Entry(sst, i as int) == Entry(sst', j as int)
  ensures c == -1 ==> lt(Entry(sst, i as int), Entry(sst', j as int))
  ensures c == 1 ==> lt(Entry(sst', j as int), Entry(sst, i as int))


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

  method MaxLens(s: seq<SSTable>)
  returns (startsLen : uint64, stringsLen: uint64)
  ensures forall i | 0 <= i < |s| :: |s[i].starts| <= startsLen as int
  ensures forall i | 0 <= i < |s| :: |s[i].strings| <= stringsLen as int

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

  method LemmaAugmentSSTable(sst: SSTable, sst': SSTable)
  requires WFSSTableMap(sst)
  requires WFSSTableMap(sst')
  requires |sst'.starts| == |sst.starts| + 2
  requires sst.starts == sst'.starts[..|sst.starts|]
  requires sst.strings == sst'.strings[..|sst.strings|]
  ensures I(sst) == I(sst')
  {
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
  requires forall j | 0 <= j < startsIdx :: startsArray[j] <= stringsIdx
  requires stringsArray.Length < 0x1000_0000_0000_0000
  requires startsArray.Length < 0x1000_0000_0000_0000
  requires startsIdx == 0 ==> stringsIdx == 0
  ensures 0 <= startsIdx' as int <= startsArray.Length
  ensures 0 <= stringsIdx' as int <= stringsArray.Length
  ensures WFSSTableMapArrays(startsArray, startsIdx', stringsArray, stringsIdx')
  ensures IArrays(startsArray, startsIdx', stringsArray, stringsIdx')
       == old(IArrays(startsArray, startsIdx, stringsArray, stringsIdx))[Entry(sst, i as int) := Define(Entry(sst, i as int + 1))]
  {
    LemmaStartEndIndices(sst, i as int);
    LemmaStartEndIndices(sst, i as int + 1);

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
    
  }

  method Flush(parent: SSTable, children: seq<SSTable>, pivots: seq<Key>)
  returns (res : seq<SSTable>)
  requires |children| == |pivots| + 1
  requires forall i, key | 0 <= i < |children| && key in I(children[i]) :: P.Route(pivots, key) == i
  //ensures |res| == |children|
  //ensures forall i, key | 0 <= i < |res| && key in I(res[i]) ==> Route(pivots, key) == i
  ensures ISeq(res) == BT.AddMessagesToBuckets(pivots, |children|, ISeq(children), I(parent))
  {
    var maxChildStartsLen: uint64, maxChildStringsLen: uint64 := MaxLens(children);
    var startsArray : array<uint64> := new uint64[maxChildStartsLen + |parent.starts| as uint64];
    var stringsArray : array<byte> := new byte[maxChildStringsLen + |parent.strings| as uint64];
    var startsIdx: uint64 := 0;
    var stringsIdx: uint64 := 0;

    res := [];

    var parentIdx: uint64 := 0;
    var childrenIdx: int := 0;
    var childIdx: uint64 := 0;
    while childrenIdx < |children|
    invariant 0 <= 2*parentIdx as int <= |parent.starts|
    invariant 0 <= childrenIdx <= |children|
    invariant childrenIdx < |children| ==> 0 <= 2*childIdx as int <= |children[childrenIdx].starts|
    invariant 0 <= startsIdx as int <= startsArray.Length
    invariant 0 <= stringsIdx as int <= stringsArray.Length
    invariant 2*parentIdx as int < |parent.starts| ==>
        forall key | key in IArrays(startsArray, startsIdx, stringsArray, stringsIdx) :: lt(key, Entry(parent, 2*parentIdx as int))
    invariant childrenIdx < |children| && 2*childIdx as int < |children[childrenIdx].starts| ==>
        forall key | key in IArrays(startsArray, startsIdx, stringsArray, stringsIdx) :: lt(key, Entry(children[childrenIdx], 2*childIdx as int))
    invariant WFSSTableMapArrays(startsArray, startsIdx, stringsArray, stringsIdx)
    invariant IArrays(startsArray, startsIdx, stringsArray, stringsIdx)
           == BT.AddMessagesToBucket(pivots, childrenIdx, IPrefix(children[childrenIdx], childIdx as int), IPrefix(parent, parentIdx as int))
    invariant ISeq(res) == BT.AddMessagesToBuckets(pivots, |res|, ISeq(children), I(parent))
    {
      if (2*parentIdx == |parent.starts| as uint64) {
        if (2*childIdx == |children[childrenIdx].starts| as uint64) {
          res := res + [SSTable(startsArray[..startsIdx], stringsArray[..stringsIdx])];

          startsIdx := 0;
          stringsIdx := 0;
          childIdx := 0;
          childrenIdx := childrenIdx + 1;
        } else {
          startsIdx, stringsIdx := WriteKeyValue(startsArray, stringsArray, startsIdx, stringsIdx, children[childrenIdx], 2*childIdx);
          childIdx := childIdx + 1; 
        }
      } else {
        if (2*childIdx == |children[childrenIdx].starts| as uint64) {
          if (childrenIdx == |children| - 1) {
            startsIdx, stringsIdx := WriteKeyValue(startsArray, stringsArray, startsIdx, stringsIdx, parent, 2*parentIdx);
            parentIdx := parentIdx + 1;
          } else {
            var c := Cmp(pivots[childrenIdx], parent, 2*parentIdx);
            if (c == -1) {
              startsIdx, stringsIdx := WriteKeyValue(startsArray, stringsArray, startsIdx, stringsIdx, parent, 2*parentIdx);
              parentIdx := parentIdx + 1;
            } else {
              res := res + [SSTable(startsArray[..startsIdx], stringsArray[..stringsIdx])];

              startsIdx := 0;
              stringsIdx := 0;
              childIdx := 0;
              childrenIdx := childrenIdx + 1;
            }
          }
        } else {
          var c := Cmp2(parent, 2*parentIdx as uint64, children[childrenIdx], 2*childIdx as uint64);
          if (c == 0) {
            startsIdx, stringsIdx := WriteKeyValue(startsArray, stringsArray, startsIdx, stringsIdx, parent, 2*parentIdx);
            childIdx := childIdx + 1;
            parentIdx := parentIdx + 1;
          } else if (c == -1) {
            startsIdx, stringsIdx := WriteKeyValue(startsArray, stringsArray, startsIdx, stringsIdx, parent, 2*parentIdx);
            parentIdx := parentIdx + 1;
          } else if (c == 1) {
            startsIdx, stringsIdx := WriteKeyValue(startsArray, stringsArray, startsIdx, stringsIdx, children[childrenIdx], 2*childIdx);
            childIdx := childIdx + 1; 
          }
        }
      }
    }
  }
}
