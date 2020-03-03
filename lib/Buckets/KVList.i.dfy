include "../Base/Message.i.dfy"
include "../Base/sequences.i.dfy"
include "../Base/Maps.s.dfy"
include "../Base/NativeArrays.s.dfy"
include "PackedStringArray.i.dfy"
include "BucketsLib.i.dfy"
include "BucketWeights.i.dfy"
//
// A list of key-message pairs, with unique, sorted keys.
// TODO(robj,thance): How is it used... in BucketImpl?
// NOTE(tjhance): this is mostly Impl-related stuff, but a bit of it is used by the Marshalling file
// TODO(tjhance): rename this to KMList because it's Keys and Messages, not Keys and Values
//
// VESTIGIAL -- do not bother trying to prove stuff here because this
// file is marked for deletion or major renovation.
//

module KVList {
  import opened ValueMessage`Internal
  import opened Lexicographic_Byte_Order
  import opened Sequences
  import opened Options
  import opened Maps
  import opened BucketsLib
  import opened BucketWeights
  import opened NativeTypes
  import NativeArrays
  import P = PivotsLib
  import SeqComparison
  import opened KeyType
  import PSA = PackedStringArray
  import Uint32_Order
  
  datatype Kvl = Kvl(keys: PSA.Psa, messages: seq<Message>)

  predicate WF(kvl: Kvl) {
    && PSA.WF(kvl.keys)
    && (forall i :: 0 <= i < PSA.psaNumStrings(kvl.keys) ==> |PSA.psaElement(kvl.keys, i)| <= MaxLen() as int)
    && IsStrictlySorted(PSA.I(kvl.keys))
    && PSA.psaNumStrings(kvl.keys) as int == |kvl.messages|
    && (forall i | 0 <= i < |kvl.messages| :: kvl.messages[i] != IdentityMessage())
  }

  function {:opaque} IMap(kvl: Kvl) : BucketMap
  requires PSA.WF(kvl.keys)
  requires PSA.psaNumStrings(kvl.keys) as int == |kvl.messages|
  ensures PSA.psaNumStrings(kvl.keys) as int == 0 ==> |IMap(kvl).Keys| == 0    // empty input -> empty output.
  ensures forall k | k in IMap(kvl).Keys :: |k| <= MaxLen() as int
  decreases PSA.psaNumStrings(kvl.keys)
  {
    if PSA.psaNumStrings(kvl.keys) == 0 then map[] else (
      IMap(Kvl(PSA.psaDropLast(kvl.keys), DropLast(kvl.messages)))[PSA.LastElement(kvl.keys) := Last(kvl.messages)]
    )
  }

  function I(kvl: Kvl) : Bucket
  requires PSA.WF(kvl.keys)
  requires PSA.psaNumStrings(kvl.keys) as int == |kvl.messages|
  ensures WF(kvl) ==> forall k | k in I(kvl).b.Keys :: |k| <= MaxLen() as int
  {
    B(IMap(kvl))
  }

  function {:opaque} ISeq(kvls: seq<Kvl>) : (s : seq<Bucket>)
  requires forall i :: 0 <= i < |kvls| ==> PSA.WF(kvls[i].keys)
  requires forall i | 0 <= i < |kvls| :: PSA.psaNumStrings(kvls[i].keys) as int == |kvls[i].messages|
  ensures |s| == |kvls|
  ensures forall i | 0 <= i < |kvls| :: s[i] == I(kvls[i])
  {
    if |kvls| == 0 then [] else ISeq(DropLast(kvls)) + [I(Last(kvls))]
  }

  function prefix(kvl: Kvl, i: int) : Kvl
  requires PSA.WF(kvl.keys)
  requires 0 <= i <= PSA.psaNumStrings(kvl.keys) as int
  requires 0 <= i <= |kvl.messages|
  {
    Kvl(PSA.psaSubSeq(kvl.keys, 0, i as uint64), kvl.messages[..i]) 
  }

  lemma WFPrefix(kvl: Kvl, i: int)
  requires WF(kvl)
  requires 0 <= i <= PSA.psaNumStrings(kvl.keys) as int
  ensures WF(prefix(kvl, i))
  {
    var pre := prefix(kvl, i);
    forall j | 0 <= j < PSA.psaNumStrings(pre.keys)
      ensures |PSA.psaElement(pre.keys, j)| <= MaxLen() as int
    {
      assert PSA.psaElement(pre.keys, j) == PSA.psaElement(kvl.keys, j);
    }
    reveal_IsStrictlySorted();
  }

  lemma IndexOfKey(kvl: Kvl, key: Key) returns (i : int)
  requires PSA.WF(kvl.keys)
  requires PSA.psaNumStrings(kvl.keys) as int == |kvl.messages|
  requires key in IMap(kvl)
  ensures 0 <= i < PSA.psaNumStrings(kvl.keys) as int
  ensures PSA.psaElement(kvl.keys, i as uint64) == key
  decreases PSA.psaNumStrings(kvl.keys) as int
  {
    reveal_IMap();
    if key == PSA.LastElement(kvl.keys) {
      i := PSA.psaNumStrings(kvl.keys) as int - 1;
    } else {
      i := IndexOfKey(Kvl(PSA.psaDropLast(kvl.keys), DropLast(kvl.messages)), key);
    }
  }

  lemma Imaps(kvl: Kvl, i: int)
  requires WF(kvl)
  requires 0 <= i < PSA.psaNumStrings(kvl.keys) as int
  ensures MapsTo(IMap(kvl), PSA.psaElement(kvl.keys, i as uint64), kvl.messages[i])
  decreases PSA.psaNumStrings(kvl.keys) as int
  {
    reveal_IMap();
    if (i == PSA.psaNumStrings(kvl.keys) as int - 1) {
    } else {
      WFPrefix(kvl, PSA.psaNumStrings(kvl.keys) as int - 1);
      Imaps(Kvl(PSA.psaDropLast(kvl.keys), DropLast(kvl.messages)), i);
      var ikeys := PSA.I(kvl.keys);
      IsStrictlySortedImpliesLt(ikeys, i, |ikeys|-1);
    }
  }

  lemma WFImpliesWFBucket(kvl: Kvl)
  requires WF(kvl)
  ensures WFBucket(I(kvl))
  decreases PSA.psaNumStrings(kvl.keys) as int
  {
    reveal_IMap();
    reveal_WFBucket();
    if PSA.psaNumStrings(kvl.keys) as int == 0 {
    } else {
      ghost var km' := Kvl(PSA.psaDropLast(kvl.keys), DropLast(kvl.messages));
      WFPrefix(kvl, PSA.psaNumStrings(kvl.keys) as int - 1);
      assert WF(km');
      WFImpliesWFBucket(km');
    }
  }

  /////////////////////////
  //// Flush
  /////////////////////////

  function append(kvl: Kvl, key: Key, value: Message) : Kvl
  requires PSA.WF(kvl.keys)
  requires |kvl.keys.offsets| < 0x1_0000_0000 - 1
  requires |kvl.keys.data| + |key| < 0x1_0000_0000
  {
    Kvl(PSA.psaAppend(kvl.keys, key), kvl.messages + [value])
  }

  lemma Iappend(kvl: Kvl, key: Key, value: Message)
  requires PSA.WF(kvl.keys)
  requires PSA.psaNumStrings(kvl.keys) as int == |kvl.messages|
  requires |kvl.keys.offsets| < 0x1_0000_0000 - 1
  requires |kvl.keys.data| + |key| < 0x1_0000_0000
  ensures IMap(append(kvl, key, value)) == IMap(kvl)[key := value]
  {
    reveal_IMap();
    var app := append(kvl, key, value);
    assert PSA.LastElement(app.keys) == key;
  }

  lemma Iprefix_append(kvl: Kvl, i: int)
  requires PSA.WF(kvl.keys)
  requires PSA.psaNumStrings(kvl.keys) as int == |kvl.messages|
  requires |kvl.keys.offsets| < 0x1_0000_0000
  requires 0 <= i < PSA.psaNumStrings(kvl.keys) as int
  requires forall j :: 0 <= j < PSA.psaNumStrings(kvl.keys) ==> |PSA.psaElement(kvl.keys, j as uint64)| <= MaxLen() as int
  ensures IMap(prefix(kvl, i + 1)) == IMap(prefix(kvl, i))[PSA.psaElement(kvl.keys, i as uint64) := kvl.messages[i]]
  {
    assert prefix(kvl, i + 1) == append(prefix(kvl, i), PSA.psaElement(kvl.keys, i as uint64), kvl.messages[i]);
    Iappend(prefix(kvl, i), PSA.psaElement(kvl.keys, i as uint64), kvl.messages[i]);
  }

  function psaLengthSoFar(psa: PSA.Psa, index: int) : int
    requires PSA.WF(psa)
    requires 0 <= index <= PSA.psaNumStrings(psa) as int
  {
    if index == PSA.psaNumStrings(psa) as int then
      |psa.data|
    else
      PSA.psaStart(psa, index as uint64) as int
  }
  
  function inputLengthSoFar(parent: Kvl, children: seq<Kvl>, parentIdx: int, childrenIdx: int, childIdx: int) : nat
    requires WF(parent)
    requires 0 < |children|
    requires forall i | 0 <= i < |children| :: WF(children[i])
    requires 0 <= parentIdx <= PSA.psaNumStrings(parent.keys) as int
    requires 0 <= childrenIdx <= |children|
    requires childrenIdx < |children| ==> 0 <= childIdx <= PSA.psaNumStrings(children[childrenIdx].keys) as int
  {
    if childrenIdx == 0 then
      psaLengthSoFar(children[0].keys, childIdx) + psaLengthSoFar(parent.keys, parentIdx)
    else if childrenIdx == |children| then
      inputLengthSoFar(parent, children, parentIdx, childrenIdx-1, PSA.psaNumStrings(children[childrenIdx-1].keys) as int)
    else
      inputLengthSoFar(parent, children, parentIdx, childrenIdx-1, PSA.psaNumStrings(children[childrenIdx-1].keys) as int) + psaLengthSoFar(children[childrenIdx].keys, childIdx)
  }

  lemma inputLengthSoFarMonotonic(parent: Kvl, children: seq<Kvl>, parentIdxA: int, childrenIdxA: int, childIdxA: int, parentIdxB: int, childrenIdxB: int, childIdxB: int)
    requires WF(parent)
    requires 0 < |children|
    requires forall i | 0 <= i < |children| :: WF(children[i])
    requires 0 <= parentIdxA <= parentIdxB <= PSA.psaNumStrings(parent.keys) as int
    requires 0 <= childrenIdxA <= childrenIdxB <= |children|
    requires childrenIdxA < |children| ==> 0 <= childIdxA <= PSA.psaNumStrings(children[childrenIdxA].keys) as int
    requires childrenIdxB < |children| ==> 0 <= childIdxB <= PSA.psaNumStrings(children[childrenIdxB].keys) as int
    requires childrenIdxA == childrenIdxB ==> childIdxA <= childIdxB
    ensures inputLengthSoFar(parent, children, parentIdxA, childrenIdxA, childIdxA) <= inputLengthSoFar(parent, children, parentIdxB, childrenIdxB, childIdxB)
  {
    if 0 < parentIdxA < PSA.psaNumStrings(parent.keys) as int && 0 < parentIdxB < PSA.psaNumStrings(parent.keys) as int {
      Uint32_Order.IsSortedImpliesLte(parent.keys.offsets, parentIdxA-1, parentIdxB-1);
    }
    assert psaLengthSoFar(parent.keys, parentIdxA) <= psaLengthSoFar(parent.keys, parentIdxB);

    if childrenIdxA == childrenIdxB < |children| {
      if 0 < childIdxA < PSA.psaNumStrings(children[childrenIdxA].keys) as int && 0 < childIdxB < PSA.psaNumStrings(children[childrenIdxA].keys) as int {
        Uint32_Order.IsSortedImpliesLte(children[childrenIdxA].keys.offsets, childIdxA-1, childIdxB-1);
      }
      assert psaLengthSoFar(children[childrenIdxA].keys, childIdxA) <= psaLengthSoFar(children[childrenIdxA].keys, childIdxB);
    }
  }

  lemma inputLengthSoFarParentIncrease(parent: Kvl, children: seq<Kvl>, parentIdx: int, childrenIdx: int, childIdx: int)
    requires WF(parent)
    requires 0 < |children|
    requires forall i | 0 <= i < |children| :: WF(children[i])
    requires 0 <= parentIdx < PSA.psaNumStrings(parent.keys) as int
    requires 0 <= childrenIdx <= |children|
    requires childrenIdx < |children| ==> 0 <= childIdx <= PSA.psaNumStrings(children[childrenIdx].keys) as int
    ensures inputLengthSoFar(parent, children, parentIdx, childrenIdx, childIdx) + |PSA.psaElement(parent.keys, parentIdx as uint64)| <= inputLengthSoFar(parent, children, parentIdx + 1, childrenIdx, childIdx)
  {
  }

  lemma inputLengthSoFarChildIncrease(parent: Kvl, children: seq<Kvl>, parentIdx: int, childrenIdx: int, childIdx: int)
    requires WF(parent)
    requires 0 < |children|
    requires forall i | 0 <= i < |children| :: WF(children[i])
    requires 0 <= parentIdx <= PSA.psaNumStrings(parent.keys) as int
    requires 0 <= childrenIdx < |children|
    requires 0 <= childIdx < PSA.psaNumStrings(children[childrenIdx].keys) as int
    ensures inputLengthSoFar(parent, children, parentIdx, childrenIdx, childIdx) + |PSA.psaElement(children[childrenIdx].keys, childIdx as uint64)| <= inputLengthSoFar(parent, children, parentIdx, childrenIdx, childIdx + 1)
  {
  }

  function inputLengthTotal(parent: Kvl, children: seq<Kvl>) : nat
    requires WF(parent)
    requires 0 < |children|
    requires forall i | 0 <= i < |children| :: WF(children[i])
  {
    inputLengthSoFar(parent, children, PSA.psaNumStrings(parent.keys) as int, |children|, 0)
  }

  lemma inputLengthGteChild(parent: Kvl, children: seq<Kvl>, childrenIdx: int)
    requires WF(parent)
    requires 0 < |children|
    requires forall i | 0 <= i < |children| :: WF(children[i])
    requires 0 <= childrenIdx < |children|
    ensures PSA.psaTotalLength(parent.keys) as int + PSA.psaTotalLength(children[childrenIdx].keys) as int <= inputLengthTotal(parent, children)
  {
    inputLengthSoFarMonotonic(parent, children, PSA.psaNumStrings(parent.keys) as int, 0, 0, PSA.psaNumStrings(parent.keys) as int, childrenIdx, 0);
    inputLengthSoFarMonotonic(parent, children, PSA.psaNumStrings(parent.keys) as int, childrenIdx, PSA.psaNumStrings(children[childrenIdx].keys) as int, PSA.psaNumStrings(parent.keys) as int, |children|, 0);
  }
  
  function psaStringsSoFar(psa: PSA.Psa, index: int) : int
    requires PSA.WF(psa)
    requires 0 <= index <= PSA.psaNumStrings(psa) as int
  {
    index
  }
  
  function inputStringsSoFar(parent: Kvl, children: seq<Kvl>, parentIdx: int, childrenIdx: int, childIdx: int) : nat
    requires WF(parent)
    requires 0 < |children|
    requires forall i | 0 <= i < |children| :: WF(children[i])
    requires 0 <= parentIdx <= PSA.psaNumStrings(parent.keys) as int
    requires 0 <= childrenIdx <= |children|
    requires childrenIdx < |children| ==> 0 <= childIdx <= PSA.psaNumStrings(children[childrenIdx].keys) as int
  {
    if childrenIdx == 0 then
      psaStringsSoFar(children[0].keys, childIdx) + psaStringsSoFar(parent.keys, parentIdx)
    else if childrenIdx == |children| then
      inputStringsSoFar(parent, children, parentIdx, childrenIdx-1, PSA.psaNumStrings(children[childrenIdx-1].keys) as int)
    else
      inputStringsSoFar(parent, children, parentIdx, childrenIdx-1, PSA.psaNumStrings(children[childrenIdx-1].keys) as int) + psaStringsSoFar(children[childrenIdx].keys, childIdx)
  }

  lemma inputStringsSoFarMonotonic(parent: Kvl, children: seq<Kvl>, parentIdxA: int, childrenIdxA: int, childIdxA: int, parentIdxB: int, childrenIdxB: int, childIdxB: int)
    requires WF(parent)
    requires 0 < |children|
    requires forall i | 0 <= i < |children| :: WF(children[i])
    requires 0 <= parentIdxA <= parentIdxB <= PSA.psaNumStrings(parent.keys) as int
    requires 0 <= childrenIdxA <= childrenIdxB <= |children|
    requires childrenIdxA < |children| ==> 0 <= childIdxA <= PSA.psaNumStrings(children[childrenIdxA].keys) as int
    requires childrenIdxB < |children| ==> 0 <= childIdxB <= PSA.psaNumStrings(children[childrenIdxB].keys) as int
    requires childrenIdxA == childrenIdxB ==> childIdxA <= childIdxB
    ensures inputStringsSoFar(parent, children, parentIdxA, childrenIdxA, childIdxA) <= inputStringsSoFar(parent, children, parentIdxB, childrenIdxB, childIdxB)
    ensures parentIdxA < parentIdxB     ==> inputStringsSoFar(parent, children, parentIdxA, childrenIdxA, childIdxA) < inputStringsSoFar(parent, children, parentIdxB, childrenIdxB, childIdxB)
  {
  }
  
  lemma inputStringsSoFarParentIncrease(parent: Kvl, children: seq<Kvl>, parentIdx: int, childrenIdx: int, childIdx: int)
    requires WF(parent)
    requires 0 < |children|
    requires forall i | 0 <= i < |children| :: WF(children[i])
    requires 0 <= parentIdx < PSA.psaNumStrings(parent.keys) as int
    requires 0 <= childrenIdx <= |children|
    requires childrenIdx < |children| ==> 0 <= childIdx <= PSA.psaNumStrings(children[childrenIdx].keys) as int
    ensures inputStringsSoFar(parent, children, parentIdx+1, childrenIdx, childIdx) == inputStringsSoFar(parent, children, parentIdx, childrenIdx, childIdx) + 1
  {
  }

  lemma inputStringsSoFarChildIncrease(parent: Kvl, children: seq<Kvl>, parentIdx: int, childrenIdx: int, childIdx: int)
    requires WF(parent)
    requires 0 < |children|
    requires forall i | 0 <= i < |children| :: WF(children[i])
    requires 0 <= parentIdx <= PSA.psaNumStrings(parent.keys) as int
    requires 0 <= childrenIdx < |children|
    requires 0 <= childIdx < PSA.psaNumStrings(children[childrenIdx].keys) as int
    ensures inputStringsSoFar(parent, children, parentIdx, childrenIdx, childIdx+1) == inputStringsSoFar(parent, children, parentIdx, childrenIdx, childIdx) + 1
  {
  }

  function inputStringsTotal(parent: Kvl, children: seq<Kvl>) : nat
    requires WF(parent)
    requires 0 < |children|
    requires forall i | 0 <= i < |children| :: WF(children[i])
  {
    inputStringsSoFar(parent, children, PSA.psaNumStrings(parent.keys) as int, |children|, 0)
  }

  lemma inputStringsGteChild(parent: Kvl, children: seq<Kvl>, childrenIdx: int)
    requires WF(parent)
    requires 0 < |children|
    requires forall i | 0 <= i < |children| :: WF(children[i])
    requires 0 <= childrenIdx < |children|
    ensures PSA.psaNumStrings(parent.keys) as int + PSA.psaNumStrings(children[childrenIdx].keys) as int <= inputStringsTotal(parent, children)
  {
    inputStringsSoFarMonotonic(parent, children, PSA.psaNumStrings(parent.keys) as int, 0, 0, PSA.psaNumStrings(parent.keys) as int, childrenIdx, 0);
    inputStringsSoFarMonotonic(parent, children, PSA.psaNumStrings(parent.keys) as int, childrenIdx, PSA.psaNumStrings(children[childrenIdx].keys) as int, PSA.psaNumStrings(parent.keys) as int, |children|, 0);
  }

  lemma appendFromParent(parent: Kvl, children: seq<Kvl>, parentIdx: int, childrenIdx: int, childIdx: int, cur: Kvl)
  requires WF(parent)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires 0 < |children|
  requires inputStringsTotal(parent, children) < 0x1_0000_0000 - 1
  requires inputLengthTotal(parent, children) < 0x1_0000_0000
  requires 0 <= parentIdx < PSA.psaNumStrings(parent.keys) as int
  requires 0 <= childrenIdx <= |children|
  requires childrenIdx < |children| ==> 0 <= childIdx <= PSA.psaNumStrings(children[childrenIdx].keys) as int
  requires childrenIdx == |children| ==> 0 == childIdx
  requires PSA.WF(cur.keys)
  requires PSA.psaNumStrings(cur.keys) as int <= inputStringsSoFar(parent, children, parentIdx, childrenIdx, childIdx)
  requires |cur.keys.data| <= inputLengthSoFar(parent, children, parentIdx, childrenIdx, childIdx)
  ensures |cur.keys.offsets| < 0x1_0000_0000 - 1
  ensures |cur.keys.data| + |PSA.psaElement(parent.keys, parentIdx as uint64)| < 0x1_0000_0000
  ensures PSA.WF(append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]).keys)
  ensures PSA.psaNumStrings(append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]).keys) as int <= inputStringsSoFar(parent, children, parentIdx+1, childrenIdx, childIdx)
  ensures |append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]).keys.data| <= inputLengthSoFar(parent, children, parentIdx+1, childrenIdx, childIdx)
  {
    inputStringsSoFarMonotonic(parent, children, parentIdx, childrenIdx, childIdx, PSA.psaNumStrings(parent.keys) as int, |children|, 0);
    inputLengthSoFarParentIncrease(parent, children, parentIdx, childrenIdx, childIdx);
    inputLengthSoFarMonotonic(parent, children, parentIdx+1, childrenIdx, childIdx, PSA.psaNumStrings(parent.keys) as int, |children|, 0);
    inputStringsSoFarParentIncrease(parent, children, parentIdx, childrenIdx, childIdx);
  }

  lemma appendFromChild(parent: Kvl, children: seq<Kvl>, parentIdx: int, childrenIdx: int, childIdx: int, cur: Kvl)
  requires WF(parent)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires 0 < |children|
  requires inputStringsTotal(parent, children) < 0x1_0000_0000 - 1
  requires inputLengthTotal(parent, children) < 0x1_0000_0000
  requires 0 <= parentIdx <= PSA.psaNumStrings(parent.keys) as int
  requires 0 <= childrenIdx < |children|
  requires 0 <= childIdx < PSA.psaNumStrings(children[childrenIdx].keys) as int
  requires PSA.WF(cur.keys)
  requires PSA.psaNumStrings(cur.keys) as int <= inputStringsSoFar(parent, children, parentIdx, childrenIdx, childIdx)
  requires |cur.keys.data| <= inputLengthSoFar(parent, children, parentIdx, childrenIdx, childIdx)
  ensures |cur.keys.offsets| < 0x1_0000_0000 - 1
  ensures |cur.keys.data| + |PSA.psaElement(children[childrenIdx].keys, childIdx as uint64)| < 0x1_0000_0000
  ensures PSA.WF(append(cur, PSA.psaElement(children[childrenIdx].keys, childIdx as uint64), children[childrenIdx].messages[childIdx]).keys)
  ensures PSA.psaNumStrings(append(cur, PSA.psaElement(children[childrenIdx].keys, childIdx as uint64), children[childrenIdx].messages[childIdx]).keys) as int <= inputStringsSoFar(parent, children, parentIdx, childrenIdx, childIdx+1)
  ensures |append(cur, PSA.psaElement(children[childrenIdx].keys, childIdx as uint64), children[childrenIdx].messages[childIdx]).keys.data| <= inputLengthSoFar(parent, children, parentIdx, childrenIdx, childIdx+1)
  {
    inputStringsSoFarMonotonic(parent, children, parentIdx, childrenIdx, childIdx, PSA.psaNumStrings(parent.keys) as int, |children|, 0);
    inputLengthSoFarChildIncrease(parent, children, parentIdx, childrenIdx, childIdx);
    inputLengthSoFarMonotonic(parent, children, parentIdx, childrenIdx, childIdx+1, PSA.psaNumStrings(parent.keys) as int, |children|, 0);
    inputStringsSoFarChildIncrease(parent, children, parentIdx, childrenIdx, childIdx);
  }

  lemma appendFromParentChildMerge(parent: Kvl, children: seq<Kvl>, parentIdx: int, childrenIdx: int, childIdx: int, cur: Kvl)
  requires WF(parent)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires 0 < |children|
  requires inputStringsTotal(parent, children) < 0x1_0000_0000 - 1
  requires inputLengthTotal(parent, children) < 0x1_0000_0000
  requires 0 <= parentIdx < PSA.psaNumStrings(parent.keys) as int
  requires 0 <= childrenIdx < |children|
  requires 0 <= childIdx < PSA.psaNumStrings(children[childrenIdx].keys) as int
  requires PSA.WF(cur.keys)
  requires PSA.psaNumStrings(cur.keys) as int <= inputStringsSoFar(parent, children, parentIdx, childrenIdx, childIdx)
  requires |cur.keys.data| <= inputLengthSoFar(parent, children, parentIdx, childrenIdx, childIdx)
  ensures |cur.keys.offsets| < 0x1_0000_0000 - 1
  ensures |cur.keys.data| + |PSA.psaElement(parent.keys, parentIdx as uint64)| < 0x1_0000_0000
  ensures PSA.WF(append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]).keys)
  ensures PSA.psaNumStrings(append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]).keys) as int <= inputStringsSoFar(parent, children, parentIdx+1, childrenIdx, childIdx + 1)
  ensures |append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]).keys.data| <= inputLengthSoFar(parent, children, parentIdx+1, childrenIdx, childIdx + 1)
  {
    inputLengthSoFarChildIncrease(parent, children, parentIdx, childrenIdx, childIdx);
    inputLengthSoFarParentIncrease(parent, children, parentIdx, childrenIdx, childIdx+1);
    inputLengthSoFarMonotonic(parent, children, parentIdx+1, childrenIdx, childIdx+1, PSA.psaNumStrings(parent.keys) as int, |children|, 0);
    inputStringsSoFarChildIncrease(parent, children, parentIdx, childrenIdx, childIdx);
    inputStringsSoFarParentIncrease(parent, children, parentIdx, childrenIdx, childIdx+1);
    inputStringsSoFarMonotonic(parent, children, parentIdx+1, childrenIdx, childIdx+1, PSA.psaNumStrings(parent.keys) as int, |children|, 0);
  }

  
  function flushIterate(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl) : seq<Kvl>
  requires WF(parent)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires PSA.WF(cur.keys)
  requires |pivots| + 1 == |children|
  requires inputStringsTotal(parent, children) < 0x1_0000_0000 - 1
  requires inputLengthTotal(parent, children) < 0x1_0000_0000
  requires 0 <= parentIdx <= PSA.psaNumStrings(parent.keys) as int
  requires 0 <= childrenIdx <= |children|
  requires childrenIdx < |children| ==> 0 <= childIdx <= PSA.psaNumStrings(children[childrenIdx].keys) as int
  requires PSA.psaNumStrings(cur.keys) as int <= inputStringsSoFar(parent, children, parentIdx, childrenIdx, childIdx)
  requires |cur.keys.data| <= inputLengthSoFar(parent, children, parentIdx, childrenIdx, childIdx)
  decreases |children| - childrenIdx
  decreases PSA.psaNumStrings(parent.keys) as int - parentIdx +
      (if childrenIdx < |children| then PSA.psaNumStrings(children[childrenIdx].keys) as int - childIdx else 0)
  {
    if childrenIdx == |children| then (
      acc
    ) else (
      var child := children[childrenIdx];

      if parentIdx == PSA.psaNumStrings(parent.keys) as int then (
        if childIdx == PSA.psaNumStrings(child.keys) as int then (
          flushIterate(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], Kvl(PSA.EmptyPsa(), []))
        //) else if |cur.keys| == 0 then (
        //  flushIterate(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [child], Kvl(PSA.EmptyPsa(), []))
        ) else (
          appendFromChild(parent, children, parentIdx, childrenIdx, childIdx, cur);
          var newcur := append(cur, PSA.psaElement(child.keys, childIdx as uint64), child.messages[childIdx]);
          flushIterate(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, newcur)
        )
      ) else (
        if childIdx == PSA.psaNumStrings(child.keys) as int then (
          if childrenIdx == |children| - 1 then (
            appendFromParent(parent, children, parentIdx, childrenIdx, childIdx, cur);
            var newcur := append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]);
            flushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, newcur)
          ) else (
            if lt(PSA.psaElement(parent.keys, parentIdx as uint64), pivots[childrenIdx]) then (
              appendFromParent(parent, children, parentIdx, childrenIdx, childIdx, cur);
              var newcur := append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]);
              flushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, newcur)
            ) else (
              flushIterate(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], Kvl(PSA.EmptyPsa(), []))
            )
          )
        ) else (
          if PSA.psaElement(child.keys, childIdx as uint64) == PSA.psaElement(parent.keys, parentIdx as uint64) then (
            var m := Merge(parent.messages[parentIdx], child.messages[childIdx]);
            if m == IdentityMessage() then (
              flushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, cur)
            ) else (
              appendFromParentChildMerge(parent, children, parentIdx, childrenIdx, childIdx, cur);
              var newcur := append(cur, PSA.psaElement(child.keys, childIdx as uint64), m);
              flushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, newcur)
            )
          ) else if lt(PSA.psaElement(child.keys, childIdx as uint64), PSA.psaElement(parent.keys, parentIdx as uint64)) then (
            appendFromChild(parent, children, parentIdx, childrenIdx, childIdx, cur);
            var newcur := append(cur, PSA.psaElement(child.keys, childIdx as uint64), child.messages[childIdx]);
            flushIterate(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, newcur)
          ) else (
            appendFromParent(parent, children, parentIdx, childrenIdx, childIdx, cur);
            var newcur := append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]);
            flushIterate(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, newcur)
          )
        )
      )
    )
  }

  function flush(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>) : seq<Kvl>
  requires WF(parent)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires |pivots| + 1 == |children|
  requires inputStringsTotal(parent, children) < 0x1_0000_0000 - 1
  requires inputLengthTotal(parent, children) < 0x1_0000_0000
  {
    flushIterate(parent, children, pivots, 0, 0, 0, [], Kvl(PSA.EmptyPsa(), []))
  }

  predicate flushIterateInv(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
  {
    && WF(parent)
    && (forall i | 0 <= i < |children| :: WF(children[i]))
    && WFBucketListProper(ISeq(children), pivots)
    && |pivots| + 1 == |children|
    && inputStringsTotal(parent, children) < 0x1_0000_0000 - 1
    && inputLengthTotal(parent, children) < 0x1_0000_0000
    && 0 <= parentIdx <= PSA.psaNumStrings(parent.keys) as int
    && 0 <= childrenIdx <= |children|
    && (childrenIdx == |children| ==> childIdx == 0)
    && (childrenIdx < |children| ==> 0 <= childIdx <= PSA.psaNumStrings(children[childrenIdx].keys) as int)
    && |acc| == childrenIdx
    && (forall i | 0 <= i < childrenIdx :: WF(acc[i]))
    && ISeq(acc) == BucketListFlushPartial(I(parent), ISeq(children), pivots, childrenIdx)
    && WF(cur)
    && PSA.psaNumStrings(cur.keys) as int <= inputStringsSoFar(parent, children, parentIdx, childrenIdx, childIdx)
    && |cur.keys.data| <= inputLengthSoFar(parent, children, parentIdx, childrenIdx, childIdx)
    && (childrenIdx < |children| ==> I(cur) == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx))
    && (childrenIdx < |children| && childIdx > 0 && parentIdx < PSA.psaNumStrings(parent.keys) as int ==> lt(PSA.psaElement(children[childrenIdx].keys, childIdx as uint64 - 1), PSA.psaElement(parent.keys, parentIdx as uint64)))
    && (childrenIdx > 0 && childrenIdx - 1 < |pivots| && parentIdx < PSA.psaNumStrings(parent.keys) as int ==> lte(pivots[childrenIdx - 1], PSA.psaElement(parent.keys, parentIdx as uint64)))
    && (parentIdx > 0 && childrenIdx < |children| && childIdx < PSA.psaNumStrings(children[childrenIdx].keys) as int ==> lt(PSA.psaElement(parent.keys, parentIdx as uint64 - 1), PSA.psaElement(children[childrenIdx].keys, childIdx as uint64)))
    && (parentIdx > 0 && childrenIdx < |pivots| ==> lt(PSA.psaElement(parent.keys, parentIdx as uint64 - 1), pivots[childrenIdx]))
  }

  lemma flushIterateCurLastLt(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  requires childrenIdx < |children|
  ensures PSA.psaNumStrings(cur.keys) as int > 0 && parentIdx < PSA.psaNumStrings(parent.keys) as int ==> lt(PSA.LastElement(cur.keys), PSA.psaElement(parent.keys, parentIdx as uint64))
  ensures PSA.psaNumStrings(cur.keys) as int > 0 && childIdx < PSA.psaNumStrings(children[childrenIdx].keys) as int ==> lt(PSA.LastElement(cur.keys), PSA.psaElement(children[childrenIdx].keys, childIdx as uint64))
  {
    reveal_IMap();
    if (PSA.psaNumStrings(cur.keys) as int > 0) {
      var lastCurKey := PSA.LastElement(cur.keys);
      assert lastCurKey in IMap(cur);
      assert lastCurKey in (IMap(prefix(parent, parentIdx)).Keys + IMap(prefix(children[childrenIdx], childIdx)).Keys);
      if lastCurKey in IMap(prefix(parent, parentIdx)).Keys {
        var i := IndexOfKey(prefix(parent, parentIdx), lastCurKey);
        assert PSA.psaElement(parent.keys, i as uint64) == lastCurKey;
        if parentIdx < PSA.psaNumStrings(parent.keys) as int {
          IsStrictlySortedImpliesLt(PSA.I(parent.keys), i, parentIdx);
        }
        if childIdx < PSA.psaNumStrings(children[childrenIdx].keys) as int {
          IsStrictlySortedImpliesLte(PSA.I(parent.keys), i, parentIdx - 1);
        }
      } else {
        var i := IndexOfKey(prefix(children[childrenIdx], childIdx), lastCurKey);
        assert PSA.psaElement(children[childrenIdx].keys, i as uint64) == lastCurKey;
        if parentIdx < PSA.psaNumStrings(parent.keys) as int {
          IsStrictlySortedImpliesLte(PSA.I(children[childrenIdx].keys), i, childIdx - 1);
        }
        if childIdx < PSA.psaNumStrings(children[childrenIdx].keys) as int {
          IsStrictlySortedImpliesLt(PSA.I(children[childrenIdx].keys), i, childIdx);
        }
      }
    }
  }

  lemma flushIterateNextsNotInPrefixes(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  requires childrenIdx < |children|
  ensures parentIdx < PSA.psaNumStrings(parent.keys) as int ==> PSA.psaElement(parent.keys, parentIdx as uint64) !in IMap(prefix(parent, parentIdx))
  ensures parentIdx < PSA.psaNumStrings(parent.keys) as int ==> PSA.psaElement(parent.keys, parentIdx as uint64) !in IMap(prefix(children[childrenIdx], childIdx))
  ensures childIdx < PSA.psaNumStrings(children[childrenIdx].keys) as int ==> PSA.psaElement(children[childrenIdx].keys, childIdx as uint64) !in IMap(prefix(parent, parentIdx))
  ensures childIdx < PSA.psaNumStrings(children[childrenIdx].keys) as int ==> PSA.psaElement(children[childrenIdx].keys, childIdx as uint64) !in IMap(prefix(children[childrenIdx], childIdx))
  {
    if parentIdx < PSA.psaNumStrings(parent.keys) as int && PSA.psaElement(parent.keys, parentIdx as uint64) in IMap(prefix(parent, parentIdx)) {
      var i := IndexOfKey(prefix(parent, parentIdx), PSA.psaElement(parent.keys, parentIdx as uint64));
      IsStrictlySortedImpliesLt(PSA.I(parent.keys), i, parentIdx);
    }
    if parentIdx < PSA.psaNumStrings(parent.keys) as int && PSA.psaElement(parent.keys, parentIdx as uint64) in IMap(prefix(children[childrenIdx], childIdx)) {
      var i := IndexOfKey(prefix(children[childrenIdx], childIdx), PSA.psaElement(parent.keys, parentIdx as uint64));
      IsStrictlySortedImpliesLte(PSA.I(children[childrenIdx].keys), i, childIdx - 1);
    }
    if childIdx < PSA.psaNumStrings(children[childrenIdx].keys) as int && PSA.psaElement(children[childrenIdx].keys, childIdx as uint64) in IMap(prefix(parent, parentIdx)) {
      var i := IndexOfKey(prefix(parent, parentIdx), PSA.psaElement(children[childrenIdx].keys, childIdx as uint64));
      IsStrictlySortedImpliesLte(PSA.I(parent.keys), i, parentIdx - 1);
    }
    if childIdx < PSA.psaNumStrings(children[childrenIdx].keys) as int && PSA.psaElement(children[childrenIdx].keys, childIdx as uint64) in IMap(prefix(children[childrenIdx], childIdx)) {
      var i := IndexOfKey(prefix(children[childrenIdx], childIdx), PSA.psaElement(children[childrenIdx].keys, childIdx as uint64));
      IsStrictlySortedImpliesLt(PSA.I(children[childrenIdx].keys), i, childIdx);
    }
  }

  lemma flushIterateAppendParent(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  requires 0 <= childrenIdx < |children|
  requires 0 <= parentIdx < PSA.psaNumStrings(parent.keys) as int
  requires childrenIdx < |pivots| ==> lt(PSA.psaElement(parent.keys, parentIdx as uint64), pivots[childrenIdx])
  requires |cur.keys.offsets| < 0x1_0000_0000 - 1
  requires |cur.keys.data| + |PSA.psaElement(parent.keys, parentIdx as uint64)| < 0x1_0000_0000
  ensures WF(append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]))
  ensures I(append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]))
      == BucketListItemFlush(I(prefix(parent, parentIdx + 1)), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx)
  {
    flushIterateCurLastLt(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
    flushIterateNextsNotInPrefixes(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
    StrictlySortedAugment(PSA.I(cur.keys), PSA.psaElement(parent.keys, parentIdx as uint64));
    BucketListItemFlushAddParentKey(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]);

    P.RouteIs(pivots, PSA.psaElement(parent.keys, parentIdx as uint64), childrenIdx);

    Iappend(cur, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]);
    Iprefix_append(parent, parentIdx);

    var app := append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]);
    var iapp := PSA.I(app.keys);
    var icur := PSA.I(cur.keys);
    var key := PSA.psaElement(parent.keys, parentIdx as uint64);
    forall i | 0 <= i < |iapp|
      ensures |PSA.psaElement(app.keys, i as uint64)| <= MaxLen() as int;
    {
      if i < |iapp| - 1 {
        assert iapp[i] == icur[i];
      } else {
        assert iapp[i] == key;
      }
    }
    PSA.psaAppendIAppend(cur.keys, key);
    
    /*assert I(append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]))
        == I(cur)[PSA.psaElement(parent.keys, parentIdx as uint64) := parent.messages[parentIdx]]
        == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx)[PSA.psaElement(parent.keys, parentIdx as uint64) := parent.messages[parentIdx]]
        == BucketListItemFlush(I(prefix(parent, parentIdx))[PSA.psaElement(parent.keys, parentIdx as uint64) := parent.messages[parentIdx]], I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx)
        == BucketListItemFlush(I(prefix(parent, parentIdx + 1)), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx);*/
  }

  lemma flushIterateAppendChild(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  requires 0 <= childrenIdx < |children|
  requires 0 <= childIdx < PSA.psaNumStrings(children[childrenIdx].keys) as int
  requires |cur.keys.offsets| < 0x1_0000_0000 - 1
  requires |cur.keys.data| + |PSA.psaElement(children[childrenIdx].keys, childIdx as uint64)| < 0x1_0000_0000
  ensures WF(append(cur, PSA.psaElement(children[childrenIdx].keys, childIdx as uint64), children[childrenIdx].messages[childIdx]))
  ensures I(append(cur, PSA.psaElement(children[childrenIdx].keys, childIdx as uint64), children[childrenIdx].messages[childIdx]))
      == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx + 1)), pivots, childrenIdx)
  {
    var child := children[childrenIdx];
    flushIterateCurLastLt(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
    flushIterateNextsNotInPrefixes(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
    StrictlySortedAugment(PSA.I(cur.keys), PSA.psaElement(child.keys, childIdx as uint64));
    BucketListItemFlushAddChildKey(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, PSA.psaElement(child.keys, childIdx as uint64), child.messages[childIdx]);

    assert WFBucketAt(I(children[childrenIdx]), pivots, childrenIdx);
    Imaps(child, childIdx);
    assert PSA.psaElement(child.keys, childIdx as uint64) in IMap(children[childrenIdx]);
    assert P.Route(pivots, PSA.psaElement(child.keys, childIdx as uint64)) == childrenIdx;

    Iappend(cur, PSA.psaElement(child.keys, childIdx as uint64), child.messages[childIdx]);
    Iprefix_append(child, childIdx);

    var app := append(cur, PSA.psaElement(children[childrenIdx].keys, childIdx as uint64), children[childrenIdx].messages[childIdx]);
    var iapp := PSA.I(app.keys);
    var icur := PSA.I(cur.keys);
    var key := PSA.psaElement(children[childrenIdx].keys, childIdx as uint64);
    forall i | 0 <= i < |iapp|
      ensures |PSA.psaElement(app.keys, i as uint64)| <= MaxLen() as int;
    {
      if i < |iapp| - 1 {
        assert iapp[i] == icur[i];
      } else {
        assert iapp[i] == key;
      }
    }
    PSA.psaAppendIAppend(cur.keys, key);

    /*assert I(append(cur, PSA.psaElement(child.keys, childIdx as uint64), child.messages[childIdx]))
        == I(cur)[PSA.psaElement(child.keys, childIdx as uint64) := child.messages[childIdx]]
        == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx)[PSA.psaElement(child.keys, childIdx as uint64) := child.messages[childIdx]]
        == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx))[PSA.psaElement(child.keys, childIdx as uint64) := child.messages[childIdx]], pivots, childrenIdx)
        == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx + 1)), pivots, childrenIdx);*/
  }

  lemma {:fuel BucketListItemFlush,0} {:fuel P.Route,0}
  flushIterateAppendParentAndChild(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  requires 0 <= childrenIdx < |children|
  requires 0 <= parentIdx < PSA.psaNumStrings(parent.keys) as int
  requires 0 <= childIdx < PSA.psaNumStrings(children[childrenIdx].keys) as int
  requires PSA.psaElement(children[childrenIdx].keys, childIdx as uint64) == PSA.psaElement(parent.keys, parentIdx as uint64)
  requires Merge(parent.messages[parentIdx], children[childrenIdx].messages[childIdx]) != IdentityMessage()
  requires |cur.keys.offsets| < 0x1_0000_0000 - 1
  requires |cur.keys.data| + |PSA.psaElement(parent.keys, parentIdx as uint64)| < 0x1_0000_0000
  ensures WF(append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), Merge(parent.messages[parentIdx], children[childrenIdx].messages[childIdx])))
  ensures I(append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), Merge(parent.messages[parentIdx], children[childrenIdx].messages[childIdx])))
      == BucketListItemFlush(I(prefix(parent, parentIdx + 1)), I(prefix(children[childrenIdx], childIdx + 1)), pivots, childrenIdx)
  {
    var child := children[childrenIdx];
    flushIterateCurLastLt(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
    flushIterateNextsNotInPrefixes(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
    StrictlySortedAugment(PSA.I(cur.keys), PSA.psaElement(child.keys, childIdx as uint64));
    BucketListItemFlushAddParentAndChildKey(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, PSA.psaElement(child.keys, childIdx as uint64), parent.messages[parentIdx], child.messages[childIdx]);

    assert WFBucketAt(I(children[childrenIdx]), pivots, childrenIdx);
    Imaps(child, childIdx);
    assert PSA.psaElement(child.keys, childIdx as uint64) in IMap(children[childrenIdx]);
    assert P.Route(pivots, PSA.psaElement(child.keys, childIdx as uint64)) == childrenIdx;

    Iappend(cur, PSA.psaElement(parent.keys, parentIdx as uint64), Merge(parent.messages[parentIdx], children[childrenIdx].messages[childIdx]));
    Iprefix_append(parent, parentIdx);
    Iprefix_append(child, childIdx);

    var app := append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), Merge(parent.messages[parentIdx], children[childrenIdx].messages[childIdx]));
    var iapp := PSA.I(app.keys);
    var icur := PSA.I(cur.keys);
    var key := PSA.psaElement(parent.keys, parentIdx as uint64);
    forall i | 0 <= i < |iapp|
      ensures |PSA.psaElement(app.keys, i as uint64)| <= MaxLen() as int;
    {
      if i < |iapp| - 1 {
        assert iapp[i] == icur[i];
      } else {
        assert iapp[i] == key;
      }
    }
    PSA.psaAppendIAppend(cur.keys, key);
    
    /*assert I(append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), Merge(parent.messages[parentIdx], children[childrenIdx].messages[childIdx])))
        == I(cur)[PSA.psaElement(parent.keys, parentIdx as uint64) := Merge(parent.messages[parentIdx], children[childrenIdx].messages[childIdx])]
        == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx)[PSA.psaElement(parent.keys, parentIdx as uint64) := Merge(parent.messages[parentIdx], children[childrenIdx].messages[childIdx])]
        == BucketListItemFlush(I(prefix(parent, parentIdx))[PSA.psaElement(parent.keys, parentIdx as uint64) := parent.messages[parentIdx]], I(prefix(children[childrenIdx], childIdx))[PSA.psaElement(child.keys, childIdx as uint64) := child.messages[childIdx]], pivots, childrenIdx)
        == BucketListItemFlush(I(prefix(parent, parentIdx + 1)), I(prefix(children[childrenIdx], childIdx + 1)), pivots, childrenIdx);*/
  }

  lemma flushIterateCurEqBucketListItemFlush(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  requires childrenIdx < |children|
  requires childIdx == PSA.psaNumStrings(children[childrenIdx].keys) as int
  requires parentIdx < PSA.psaNumStrings(parent.keys) as int ==> childrenIdx < |pivots| && lte(pivots[childrenIdx], PSA.psaElement(parent.keys, parentIdx as uint64))
  ensures I(cur) == BucketListItemFlush(I(parent), I(children[childrenIdx]), pivots, childrenIdx)
  {
    var pre := prefix(parent, parentIdx);
    forall key | P.Route(pivots, key) == childrenIdx
    ensures MapsAgreeOnKey(IMap(prefix(parent, parentIdx)), IMap(parent), key)
    {
      WFPrefix(parent, parentIdx);
      if (key in IMap(prefix(parent, parentIdx))) {
        var i := IndexOfKey(prefix(parent, parentIdx), key);
        assert PSA.psaElement(parent.keys, i as uint64) == PSA.psaElement(pre.keys, i as uint64);
        Imaps(parent, i);
        Imaps(prefix(parent, parentIdx), i);
      } else if (key in IMap(parent)) {
        var i := IndexOfKey(parent, key);
        if (i < parentIdx) {
          assert PSA.psaElement(parent.keys, i as uint64) == PSA.psaElement(pre.keys, i as uint64);
          Imaps(parent, i);
          Imaps(prefix(parent, parentIdx), i);
        } else {
          assert lt(PSA.psaElement(parent.keys, i as uint64), pivots[childrenIdx]);
          assert lte(pivots[childrenIdx], PSA.psaElement(parent.keys, parentIdx as uint64));
          IsStrictlySortedImpliesLte(PSA.I(parent.keys), parentIdx, i);
          assert false;
        }
      }
    }
    BucketListItemFlushEq(I(prefix(parent, parentIdx)), I(parent), I(prefix(children[childrenIdx], childIdx)), pivots, childrenIdx);
    assert prefix(children[childrenIdx], childIdx) == children[childrenIdx];
  }

  lemma flushIteratepivotLteChildKey0(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  ensures childrenIdx < |pivots| && PSA.psaNumStrings(children[childrenIdx + 1].keys) as int > 0 ==> lte(pivots[childrenIdx], PSA.FirstElement(children[childrenIdx + 1].keys))
  {
    if childrenIdx < |pivots| && PSA.psaNumStrings(children[childrenIdx + 1].keys) as int > 0 {
      Imaps(children[childrenIdx + 1], 0);
      assert P.Route(pivots, PSA.FirstElement(children[childrenIdx + 1].keys)) == childrenIdx + 1;
    }
  }

  lemma flushIterateIEmptyEqBucketListItemFlush(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  requires childrenIdx + 1 < |children| && parentIdx > 0 ==> lt(PSA.psaElement(parent.keys, parentIdx as uint64 - 1), pivots[childrenIdx])
  ensures childrenIdx + 1 < |children| ==>
         I(Kvl(PSA.EmptyPsa(),[])).b
      == BucketListItemFlush(I(prefix(parent, parentIdx)), I(prefix(children[childrenIdx + 1], 0)), pivots, childrenIdx + 1).b
  {
    forall key | key in IMap(prefix(parent, parentIdx))
    ensures P.Route(pivots, key) != childrenIdx + 1
    {
      var i := IndexOfKey(prefix(parent, parentIdx), key);
      IsStrictlySortedImpliesLte(PSA.I(parent.keys), i, parentIdx - 1);
    }
  }

  lemma flushIterateRes(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>,
      parentIdx: int, childrenIdx: int, childIdx: int, acc: seq<Kvl>, cur: Kvl)
  requires flushIterateInv(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur)
  ensures var f := flushIterate(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
      && (forall i | 0 <= i < |f| :: WF(f[i]))
      && ISeq(f) == BucketListFlush(I(parent), ISeq(children), pivots)
  decreases |children| - childrenIdx
  decreases PSA.psaNumStrings(parent.keys) as int - parentIdx +
      (if childrenIdx < |children| then PSA.psaNumStrings(children[childrenIdx].keys) as int - childIdx else 0)
  {
    inputStringsSoFarMonotonic(parent, children, parentIdx, childrenIdx, childIdx, PSA.psaNumStrings(parent.keys) as int, |children|, 0);
    inputLengthSoFarMonotonic(parent, children, parentIdx, childrenIdx, childIdx, PSA.psaNumStrings(parent.keys) as int, |children|, 0);
    
    if childrenIdx == |children| {
    } else {
      var child := children[childrenIdx];

      if parentIdx + 1 < PSA.psaNumStrings(parent.keys) as int {
        IsStrictlySortedImpliesLt(PSA.I(parent.keys), parentIdx, parentIdx + 1);
      }
      if childrenIdx + 1 < |pivots| {
        IsStrictlySortedImpliesLt(pivots, childrenIdx, childrenIdx + 1);
      }
      if childIdx + 1 < PSA.psaNumStrings(child.keys) as int {
        IsStrictlySortedImpliesLt(PSA.I(child.keys), childIdx, childIdx + 1);
      }
      if childIdx < PSA.psaNumStrings(child.keys) as int {
        Imaps(child, childIdx);
        assert P.Route(pivots, PSA.psaElement(child.keys, childIdx as uint64)) == childrenIdx;
      }

      if parentIdx == PSA.psaNumStrings(parent.keys) as int {
        if childIdx == PSA.psaNumStrings(child.keys) as int {
          flushIterateCurEqBucketListItemFlush(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
          flushIterateIEmptyEqBucketListItemFlush(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
          flushIteratepivotLteChildKey0(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
          flushIterateRes(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], Kvl(PSA.EmptyPsa(), []));
        //} else if |cur| == 0 {
        //  flushIterateRes(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [child], Kvl(PSA.EmptyPsa(), []));
        } else {
          appendFromChild(parent, children, parentIdx, childrenIdx, childIdx, cur);          
          flushIterateAppendChild(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
          flushIterateRes(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, append(cur, PSA.psaElement(child.keys, childIdx as uint64), child.messages[childIdx]));
        }
      } else {
        if childIdx == PSA.psaNumStrings(child.keys) as int {
          if childrenIdx == |children| - 1 {
            appendFromParent(parent, children, parentIdx, childrenIdx, childIdx, cur);
            flushIterateAppendParent(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
            flushIterateRes(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]));
          } else {
            if lt(PSA.psaElement(parent.keys, parentIdx as uint64), pivots[childrenIdx]) {
              appendFromParent(parent, children, parentIdx, childrenIdx, childIdx, cur);
              flushIterateAppendParent(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
              flushIterateRes(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]));
            } else {
              flushIterateCurEqBucketListItemFlush(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
              flushIterateIEmptyEqBucketListItemFlush(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
              flushIteratepivotLteChildKey0(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
              flushIterateRes(parent, children, pivots, parentIdx, childrenIdx + 1, 0, acc + [cur], Kvl(PSA.EmptyPsa(), []));
            }
          }
        } else {
          if PSA.psaElement(child.keys, childIdx as uint64) == PSA.psaElement(parent.keys, parentIdx as uint64) {
            var m := Merge(parent.messages[parentIdx], child.messages[childIdx]);
            if m == IdentityMessage() {
              flushIterateRes(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, cur);
            } else {
              appendFromParentChildMerge(parent, children, parentIdx, childrenIdx, childIdx, cur);
              flushIterateAppendParentAndChild(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
              flushIterateRes(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx + 1, acc, append(cur, PSA.psaElement(child.keys, childIdx as uint64), m));
            }
          } else if lt(PSA.psaElement(child.keys, childIdx as uint64), PSA.psaElement(parent.keys, parentIdx as uint64)) {
            appendFromChild(parent, children, parentIdx, childrenIdx, childIdx, cur);
            flushIterateAppendChild(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
            flushIterateRes(parent, children, pivots, parentIdx, childrenIdx, childIdx + 1, acc, append(cur, PSA.psaElement(child.keys, childIdx as uint64), child.messages[childIdx]));
          } else {
            appendFromParent(parent, children, parentIdx, childrenIdx, childIdx, cur);
            flushIterateAppendParent(parent, children, pivots, parentIdx, childrenIdx, childIdx, acc, cur);
            flushIterateRes(parent, children, pivots, parentIdx + 1, childrenIdx, childIdx, acc, append(cur, PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx]));
          }
        }
      }
    }
  }

  lemma flushRes(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>)
  requires WF(parent)
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires WFBucketListProper(ISeq(children), pivots)
  requires inputStringsTotal(parent, children) < 0x1_0000_0000 - 1
  requires inputLengthTotal(parent, children) < 0x1_0000_0000
  ensures var f := flush(parent, children, pivots);
      && (forall i | 0 <= i < |f| :: WF(f[i]))
      && ISeq(f) == BucketListFlush(I(parent), ISeq(children), pivots)
  {
    reveal_IMap();
    assert BucketListItemFlush(B(map[]), B(map[]), pivots, 0).b == map[];
    flushIterateRes(parent, children, pivots, 0, 0, 0, [], Kvl(PSA.EmptyPsa(), []));
  }

  method appendString(num_strings: uint64, offsets: array<uint32>, total_length: uint32, data: array<byte>, str: Key)
    returns (new_total_length: uint32)
    requires num_strings as int < offsets.Length < 0x1_0000_0000
    requires total_length as int + |str| <= data.Length < 0x1_0000_0000
    ensures offsets[..num_strings] == old(offsets[..num_strings])
    ensures offsets[num_strings] == total_length + |str| as uint32
    ensures data[..total_length] == old(data[..total_length])
    ensures data[total_length..total_length + |str| as uint32] == str
    ensures new_total_length == total_length + |str| as uint32
    modifies offsets, data
  {
    NativeArrays.CopySeqIntoArray(str, 0, data, total_length as uint64, |str| as uint64);
    offsets[num_strings] := total_length + |str| as uint32;
    new_total_length := total_length + |str| as uint32;
  }
  
  method Flush(parent: Kvl, children: seq<Kvl>, pivots: seq<Key>)
  returns (f : seq<Kvl>)
  requires WF(parent)
  requires 0 < |children|
  requires forall i | 0 <= i < |children| :: WF(children[i])
  requires inputStringsTotal(parent, children) < 0x1_0000_0000 - 1
  requires inputLengthTotal(parent, children) < 0x1_0000_0000
  requires WFBucketListProper(ISeq(children), pivots)
  requires |children| < 0x1_0000_0000_0000_0000
  requires forall i | 0 <= i < |children| :: PSA.psaNumStrings(children[i].keys) as int + PSA.psaNumStrings(parent.keys) as int < 0x8000_0000_0000_0000
  ensures forall i | 0 <= i < |f| :: WF(f[i])
  ensures ISeq(f) == BucketListFlush(I(parent), ISeq(children), pivots)
  ensures f == flush(parent, children, pivots)
  {
    assert PSA.psaNumStrings(children[0].keys) as int + PSA.psaNumStrings(parent.keys) as int < 0x8000_0000_0000_0000;

    var maxChildNumStrings: uint64 := PSA.psaNumStrings(children[0].keys);
    var maxChildLen: uint64 := PSA.psaTotalLength(children[0].keys);
    var idx: uint64 := 0;
    ghost var len_rep: nat := 0;
    ghost var str_rep: nat := 0;
    while idx < |children| as uint64
    invariant 0 <= idx as int <= |children|
    invariant forall i | 0 <= i < idx as int :: PSA.psaNumStrings(children[i].keys) as int <= maxChildNumStrings as int
    invariant forall i | 0 <= i < idx as int :: PSA.psaTotalLength(children[i].keys) as int <= maxChildLen as int
    invariant maxChildNumStrings as int + PSA.psaNumStrings(parent.keys) as int < 0x8000_0000_0000_0000
    invariant len_rep < |children| 
    invariant maxChildLen == PSA.psaTotalLength(children[len_rep].keys)
    invariant str_rep < |children| 
    invariant maxChildNumStrings == PSA.psaNumStrings(children[str_rep].keys)
    {
      if PSA.psaNumStrings(children[idx].keys) > maxChildNumStrings {
        str_rep := idx as nat;
        maxChildNumStrings := PSA.psaNumStrings(children[idx].keys);
      }
      if maxChildLen < PSA.psaTotalLength(children[idx].keys) {
        len_rep := idx as nat;
        maxChildLen := PSA.psaTotalLength(children[idx].keys);
      }
      idx := idx + 1;
    }

    inputLengthGteChild(parent, children, len_rep);
    assert maxChildLen as int + PSA.psaTotalLength(parent.keys) as int <= inputLengthTotal(parent, children);

    inputStringsGteChild(parent, children, str_rep);
    assert maxChildNumStrings as int + PSA.psaNumStrings(parent.keys) as int <= inputStringsTotal(parent, children);

    
    var parentIdx: uint64 := 0;
    var childrenIdx: uint64 := 0;
    var childIdx: uint64 := 0;
    var acc := [];
    
    var cur_keys_data := new byte[maxChildLen + PSA.psaTotalLength(parent.keys) ];
    var cur_keys_offsets := new uint32[maxChildNumStrings + PSA.psaNumStrings(parent.keys) ];
    var cur_keys_numstrings: uint64 := 0;
    var cur_keys_totallen: uint32 := 0;

    var cur_values := new Message[maxChildNumStrings + PSA.psaNumStrings(parent.keys) ];

    while childrenIdx < |children| as uint64
    invariant cur_keys_numstrings <= cur_keys_offsets.Length as uint64
    invariant cur_keys_totallen <= cur_keys_data.Length as uint32
    invariant PSA.WF(PSA.Psa(cur_keys_offsets[..cur_keys_numstrings], cur_keys_data[..cur_keys_totallen]))
    invariant 0 <= parentIdx as int <= PSA.psaNumStrings(parent.keys) as int
    invariant 0 <= childrenIdx as int <= |children|
    invariant (childrenIdx as int < |children| ==> 0 <= childIdx as int <= PSA.psaNumStrings(children[childrenIdx].keys) as int)
    invariant 0 <= cur_keys_numstrings
    invariant childrenIdx as int < |children| ==> cur_keys_numstrings as int <= parentIdx as int + childIdx as int
    invariant childrenIdx as int == |children| ==> cur_keys_numstrings == 0

    invariant cur_keys_numstrings as int <= parentIdx as int + childIdx as int
    invariant cur_keys_numstrings as int <= inputStringsSoFar(parent, children, parentIdx as int, childrenIdx as int, childIdx as int)
    invariant childrenIdx as int < |children|
    ==> cur_keys_totallen as uint64 <= PSA.psaTotalLength(PSA.psaSubSeq(parent.keys, 0, parentIdx)) + PSA.psaTotalLength(PSA.psaSubSeq(children[childrenIdx].keys, 0, childIdx));
    invariant cur_keys_totallen as int <= inputLengthSoFar(parent, children, parentIdx as int, childrenIdx as int, childIdx as int)

    invariant flushIterate(parent, children, pivots, parentIdx as int, childrenIdx as int, childIdx as int, acc, Kvl(PSA.Psa(cur_keys_offsets[..cur_keys_numstrings], cur_keys_data[..cur_keys_totallen]), cur_values[..cur_keys_numstrings]))
        == flush(parent, children, pivots)
    decreases |children| - childrenIdx as int
    decreases PSA.psaNumStrings(parent.keys) as int - parentIdx as int +
        (if childrenIdx as int < |children| then PSA.psaNumStrings(children[childrenIdx].keys) as int - childIdx as int else 0)
    {
      var child := children[childrenIdx];
      if parentIdx == PSA.psaNumStrings(parent.keys)  {
        if childIdx == PSA.psaNumStrings(child.keys)  {
          childrenIdx := childrenIdx + 1;
          childIdx := 0;
          acc := acc + [Kvl(PSA.Psa(cur_keys_offsets[..cur_keys_numstrings], cur_keys_data[..cur_keys_totallen]), cur_values[..cur_keys_numstrings])];
          cur_keys_numstrings := 0;
          cur_keys_totallen := 0;
        } else {
          ghost var old_cur_keys_totallen := cur_keys_totallen;
          cur_keys_totallen := appendString(cur_keys_numstrings, cur_keys_offsets, cur_keys_totallen, cur_keys_data, PSA.psaElement(child.keys, childIdx as uint64));
          cur_values[cur_keys_numstrings] := child.messages[childIdx];
          assert append(Kvl(PSA.Psa(cur_keys_offsets[..cur_keys_numstrings], cur_keys_data[..old_cur_keys_totallen]), cur_values[..cur_keys_numstrings]), PSA.psaElement(child.keys, childIdx as uint64), child.messages[childIdx])
            == Kvl(PSA.Psa(cur_keys_offsets[..cur_keys_numstrings+1], cur_keys_data[..cur_keys_totallen]), cur_values[..cur_keys_numstrings+1]);
          inputStringsSoFarChildIncrease(parent, children, parentIdx as int, childrenIdx as int, childIdx as int);
          inputLengthSoFarChildIncrease(parent, children, parentIdx as int, childrenIdx as int, childIdx as int);
          childIdx := childIdx + 1;
          cur_keys_numstrings := cur_keys_numstrings + 1;
        }
      } else {
        if childIdx == PSA.psaNumStrings(child.keys)  {
          if childrenIdx == |children| as uint64 - 1 {
            ghost var old_cur_keys_totallen := cur_keys_totallen;
            cur_keys_totallen := appendString(cur_keys_numstrings, cur_keys_offsets, cur_keys_totallen, cur_keys_data, PSA.psaElement(parent.keys, parentIdx as uint64));
            cur_values[cur_keys_numstrings] := parent.messages[parentIdx];
            assert append(Kvl(PSA.Psa(cur_keys_offsets[..cur_keys_numstrings], cur_keys_data[..old_cur_keys_totallen]), cur_values[..cur_keys_numstrings]), PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx])
              == Kvl(PSA.Psa(cur_keys_offsets[..cur_keys_numstrings+1], cur_keys_data[..cur_keys_totallen]), cur_values[..cur_keys_numstrings+1]);
            inputStringsSoFarParentIncrease(parent, children, parentIdx as int, childrenIdx as int, childIdx as int);
            inputLengthSoFarParentIncrease(parent, children, parentIdx as int, childrenIdx as int, childIdx as int);
            parentIdx := parentIdx + 1;
            cur_keys_numstrings := cur_keys_numstrings + 1;
          } else {
            var c := cmp(PSA.psaElement(parent.keys, parentIdx as uint64), pivots[childrenIdx]);
            if c < 0 {
              ghost var old_cur_keys_totallen := cur_keys_totallen;
              assert cur_keys_totallen as int + |PSA.psaElement(parent.keys, parentIdx as uint64)| <= cur_keys_data.Length;
              cur_keys_totallen := appendString(cur_keys_numstrings, cur_keys_offsets, cur_keys_totallen, cur_keys_data, PSA.psaElement(parent.keys, parentIdx as uint64));
              cur_values[cur_keys_numstrings] := parent.messages[parentIdx];
              assert append(Kvl(PSA.Psa(cur_keys_offsets[..cur_keys_numstrings], cur_keys_data[..old_cur_keys_totallen]), cur_values[..cur_keys_numstrings]), PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx])
                == Kvl(PSA.Psa(cur_keys_offsets[..cur_keys_numstrings+1], cur_keys_data[..cur_keys_totallen]), cur_values[..cur_keys_numstrings+1]);
              inputStringsSoFarParentIncrease(parent, children, parentIdx as int, childrenIdx as int, childIdx as int);
              inputLengthSoFarParentIncrease(parent, children, parentIdx as int, childrenIdx as int, childIdx as int);
              parentIdx := parentIdx + 1;
              cur_keys_numstrings := cur_keys_numstrings + 1;
            } else {
              acc := acc + [Kvl(PSA.Psa(cur_keys_offsets[..cur_keys_numstrings], cur_keys_data[..cur_keys_totallen]), cur_values[..cur_keys_numstrings])];
              childrenIdx := childrenIdx + 1;
              childIdx := 0;
              cur_keys_numstrings := 0;
              cur_keys_totallen := 0;
            }
          }
        } else {
          var c := cmp(PSA.psaElement(child.keys, childIdx as uint64), PSA.psaElement(parent.keys, parentIdx as uint64));
          if c == 0 {
            var m := Merge(parent.messages[parentIdx], child.messages[childIdx]);
            inputStringsSoFarParentIncrease(parent, children, parentIdx as int, childrenIdx as int, childIdx as int);
            inputStringsSoFarChildIncrease(parent, children, parentIdx as int + 1, childrenIdx as int, childIdx as int);
            inputLengthSoFarParentIncrease(parent, children, parentIdx as int, childrenIdx as int, childIdx as int);
            inputLengthSoFarChildIncrease(parent, children, parentIdx as int + 1, childrenIdx as int, childIdx as int);
            if m == IdentityMessage() {
              parentIdx := parentIdx + 1;
              childIdx := childIdx + 1;
            } else {
              ghost var old_cur_keys_totallen := cur_keys_totallen;
              cur_keys_totallen := appendString(cur_keys_numstrings, cur_keys_offsets, cur_keys_totallen, cur_keys_data, PSA.psaElement(parent.keys, parentIdx as uint64));
              cur_values[cur_keys_numstrings] := m;
              assert append(Kvl(PSA.Psa(cur_keys_offsets[..cur_keys_numstrings], cur_keys_data[..old_cur_keys_totallen]), cur_values[..cur_keys_numstrings]), PSA.psaElement(parent.keys, parentIdx as uint64), m)
                == Kvl(PSA.Psa(cur_keys_offsets[..cur_keys_numstrings+1], cur_keys_data[..cur_keys_totallen]), cur_values[..cur_keys_numstrings+1]);
              cur_keys_numstrings := cur_keys_numstrings + 1;
              parentIdx := parentIdx + 1;
              childIdx := childIdx + 1;
            }
          } else if c < 0 {
            ghost var old_cur_keys_totallen := cur_keys_totallen;
            cur_keys_totallen := appendString(cur_keys_numstrings, cur_keys_offsets, cur_keys_totallen, cur_keys_data, PSA.psaElement(child.keys, childIdx as uint64));
            cur_values[cur_keys_numstrings] := child.messages[childIdx];
            assert append(Kvl(PSA.Psa(cur_keys_offsets[..cur_keys_numstrings], cur_keys_data[..old_cur_keys_totallen]), cur_values[..cur_keys_numstrings]), PSA.psaElement(child.keys, childIdx as uint64), child.messages[childIdx])
              == Kvl(PSA.Psa(cur_keys_offsets[..cur_keys_numstrings+1], cur_keys_data[..cur_keys_totallen]), cur_values[..cur_keys_numstrings+1]);
            inputStringsSoFarChildIncrease(parent, children, parentIdx as int, childrenIdx as int, childIdx as int);
            inputLengthSoFarChildIncrease(parent, children, parentIdx as int, childrenIdx as int, childIdx as int);
            childIdx := childIdx + 1;
            cur_keys_numstrings := cur_keys_numstrings + 1;
          } else {
            ghost var old_cur_keys_totallen := cur_keys_totallen;
            cur_keys_totallen := appendString(cur_keys_numstrings, cur_keys_offsets, cur_keys_totallen, cur_keys_data, PSA.psaElement(parent.keys, parentIdx as uint64));
            cur_values[cur_keys_numstrings] := parent.messages[parentIdx];
            assert append(Kvl(PSA.Psa(cur_keys_offsets[..cur_keys_numstrings], cur_keys_data[..old_cur_keys_totallen]), cur_values[..cur_keys_numstrings]), PSA.psaElement(parent.keys, parentIdx as uint64), parent.messages[parentIdx])
              == Kvl(PSA.Psa(cur_keys_offsets[..cur_keys_numstrings+1], cur_keys_data[..cur_keys_totallen]), cur_values[..cur_keys_numstrings+1]);
            inputStringsSoFarParentIncrease(parent, children, parentIdx as int, childrenIdx as int, childIdx as int);
            inputLengthSoFarParentIncrease(parent, children, parentIdx as int, childrenIdx as int, childIdx as int);
            parentIdx := parentIdx + 1;
            cur_keys_numstrings := cur_keys_numstrings + 1;
          }
        }
      }
    }

    flushRes(parent, children, pivots);
    return acc;
  }
  
  /////////////////////////
  //// Query
  /////////////////////////

  method Query(kvl: Kvl, key: Key) returns (m: Option<Message>)
  requires WF(kvl)
  requires PSA.psaNumStrings(kvl.keys) as int < 0x8000_0000_0000_0000
  ensures m.None? ==> key !in I(kvl).b
  ensures m.Some? ==> key in I(kvl).b && I(kvl).b[key] == m.value
  {
    var lo: uint64 := 0;
    var hi: uint64 := PSA.psaNumStrings(kvl.keys) ;

    while lo < hi
    invariant 0 <= lo as int <= PSA.psaNumStrings(kvl.keys) as int
    invariant 0 <= hi as int <= PSA.psaNumStrings(kvl.keys) as int
    invariant lo > 0 ==> lt(PSA.psaElement(kvl.keys, lo-1), key)
    invariant hi as int < PSA.psaNumStrings(kvl.keys) as int ==> lt(key, PSA.psaElement(kvl.keys, hi))
    decreases hi as int - lo as int
    {
      var mid: uint64 := (lo + hi) / 2;
      var c := cmp(key, PSA.psaElement(kvl.keys, mid));
      if c == 0 {
        m := Some(kvl.messages[mid]);
        Imaps(kvl, mid as int);
        return;
      } else if (c < 0) {
        hi := mid;
      } else {
        lo := mid + 1;
      }
    }

    if (key in IMap(kvl)) {
      ghost var j := IndexOfKey(kvl, key);
      if (lo > 0) { IsStrictlySortedImpliesLtIndices(PSA.I(kvl.keys), lo as int - 1, j as int); }
      if (hi as int < PSA.psaNumStrings(kvl.keys) as int) { IsStrictlySortedImpliesLtIndices(PSA.I(kvl.keys), j as int, hi as int); }
    }

    m := None;
  }

  /////////////////////////
  //// Binary searching
  /////////////////////////

  lemma BinaryLow(keys: seq<Key>, key: Key, i: int)
    requires IsStrictlySorted(keys)
    requires 0 <= i < |keys|
    requires lte(keys[i], key)
    ensures forall j | 0 <= j < i :: lt(keys[j], key)
  {
    reveal_IsStrictlySorted();
  }
  
  lemma BinaryHi(keys: seq<Key>, key: Key, i: int)
    requires IsStrictlySorted(keys)
    requires 0 <= i < |keys|
    requires lte(key, keys[i])
    ensures forall j | i < j < |keys| :: lt(key, keys[j])
  {
    reveal_IsStrictlySorted();
  }
  
  method IndexOfFirstKeyGte(kvl: Kvl, key: Key)
  returns (idx: uint64)
  requires WF(kvl)
  requires PSA.psaNumStrings(kvl.keys) as int < 0x8000_0000_0000_0000
  ensures 0 <= idx as int <= PSA.psaNumStrings(kvl.keys) as int
  ensures forall i | 0 <= i < idx as int :: lt(PSA.psaElement(kvl.keys, i as uint64), key)
  ensures forall i | idx as int <= i as int < PSA.psaNumStrings(kvl.keys) as int :: lte(key, PSA.psaElement(kvl.keys, i))
  {
    var lo: uint64 := 0;
    var hi: uint64 := PSA.psaNumStrings(kvl.keys) ;

    while lo < hi
    invariant 0 <= lo as int <= PSA.psaNumStrings(kvl.keys) as int
    invariant 0 <= hi as int <= PSA.psaNumStrings(kvl.keys) as int
    invariant forall i | 0 <= i < lo as int :: lt(PSA.psaElement(kvl.keys, i as uint64), key)
    invariant forall i | hi as int <= i < PSA.psaNumStrings(kvl.keys) as int :: lte(key, PSA.psaElement(kvl.keys, i as uint64))
    decreases hi as int - lo as int
    {
      var mid: uint64 := (lo + hi) / 2;
      var c := cmp(key, PSA.psaElement(kvl.keys, mid));
      if (c > 0) {
        lo := mid + 1;
        BinaryLow(PSA.I(kvl.keys), key, mid as int);
        assert forall i | 0 <= i < lo :: PSA.psaElement(kvl.keys, i) == PSA.I(kvl.keys)[i];
      } else {
        hi := mid;
        BinaryHi(PSA.I(kvl.keys), key, mid as int);
        assert forall i | lo <= i < PSA.psaNumStrings(kvl.keys) :: PSA.psaElement(kvl.keys, i) == PSA.I(kvl.keys)[i];
      }
    }

    idx := lo;
  }

  method IndexOfFirstKeyGt(kvl: Kvl, key: Key)
  returns (idx: uint64)
  requires WF(kvl)
  requires PSA.psaNumStrings(kvl.keys) as int < 0x8000_0000_0000_0000
  ensures 0 <= idx as int <= PSA.psaNumStrings(kvl.keys) as int
  ensures forall i | 0 <= i < idx as int :: lte(PSA.psaElement(kvl.keys, i as uint64), key)
  ensures forall i | idx as int <= i as int < PSA.psaNumStrings(kvl.keys) as int :: lt(key, PSA.psaElement(kvl.keys, i))
  {
    var lo: uint64 := 0;
    var hi: uint64 := PSA.psaNumStrings(kvl.keys) ;

    while lo < hi
    invariant 0 <= lo as int <= PSA.psaNumStrings(kvl.keys) as int
    invariant 0 <= hi as int <= PSA.psaNumStrings(kvl.keys) as int
    invariant forall i | 0 <= i < lo as int :: lte(PSA.psaElement(kvl.keys, i as uint64), key)
    invariant forall i | hi as int <= i < PSA.psaNumStrings(kvl.keys) as int :: lt(key, PSA.psaElement(kvl.keys, i as uint64))
    decreases hi as int - lo as int
    {
      reveal_IsStrictlySorted();

      var mid: uint64 := (lo + hi) / 2;
      var c := cmp(key, PSA.psaElement(kvl.keys, mid));
      if (c >= 0) {
        lo := mid + 1;
        BinaryLow(PSA.I(kvl.keys), key, mid as int);
        assert forall i | 0 <= i < lo :: PSA.psaElement(kvl.keys, i) == PSA.I(kvl.keys)[i];
      } else {
        hi := mid;
        BinaryHi(PSA.I(kvl.keys), key, mid as int);
        assert forall i | lo <= i < PSA.psaNumStrings(kvl.keys) :: PSA.psaElement(kvl.keys, i) == PSA.I(kvl.keys)[i];
      }
    }

    idx := lo;
  }

  /////////////////////////
  //// Splitting
  /////////////////////////

  method SplitLeft(kvl: Kvl, pivot: Key)
  returns (left: Kvl)
  requires WF(kvl)
  requires PSA.psaNumStrings(kvl.keys) as int < 0x8000_0000_0000_0000
  ensures WF(left)
  ensures I(left) == SplitBucketLeft(I(kvl), pivot)
  {
    reveal_SplitBucketLeft();
    var idx := IndexOfFirstKeyGte(kvl, pivot);
    var newkeys := PSA.PsaPrefix(kvl.keys, idx);
    left := Kvl(newkeys, kvl.messages[..idx]);

    reveal_IsStrictlySorted();
    ghost var ikeys := PSA.I(kvl.keys);
    ghost var inewkeys := PSA.I(newkeys);
    forall i | 0 <= i < PSA.psaNumStrings(newkeys)
      ensures PSA.psaElement(newkeys, i) == PSA.psaElement(kvl.keys, i)
    {
      calc {
        PSA.psaElement(newkeys, i);
        inewkeys[i];
        ikeys[i];
        PSA.psaElement(kvl.keys, i);
      }
    }
    
    ghost var a := IMap(left);
    ghost var b := SplitBucketLeft(I(kvl), pivot).b;

    forall key | key in a
    ensures key in b
    ensures a[key] == b[key]
    {
      ghost var i := IndexOfKey(left, key);
      Imaps(left, i);
      Imaps(kvl, i);
    }

    forall key | key in b
    ensures key in a
    {
      ghost var i := IndexOfKey(kvl, key);
      Imaps(left, i);
      Imaps(kvl, i);
    }

    assert a == b;
  }

  method SplitRight(kvl: Kvl, pivot: Key)
  returns (right: Kvl)
  requires WF(kvl)
  requires PSA.psaNumStrings(kvl.keys) as int < 0x8000_0000_0000_0000
  ensures WF(right)
  ensures I(right) == SplitBucketRight(I(kvl), pivot)
  {
    reveal_SplitBucketRight();
    var idx := IndexOfFirstKeyGte(kvl, pivot);
    var newkeys := PSA.PsaSuffix(kvl.keys, idx);
    right := Kvl(newkeys, kvl.messages[idx..]);

    reveal_IsStrictlySorted();
    ghost var ikeys := PSA.I(kvl.keys);
    ghost var inewkeys := PSA.I(newkeys);
    forall i | 0 <= i < PSA.psaNumStrings(newkeys)
      ensures PSA.psaElement(newkeys, i) == PSA.psaElement(kvl.keys, idx + i)
    {
      calc {
        PSA.psaElement(newkeys, i);
        inewkeys[i];
        ikeys[idx + i];
        PSA.psaElement(kvl.keys, idx + i);
      }
    }

    ghost var a := IMap(right);
    ghost var b := SplitBucketRight(I(kvl), pivot).b;

    forall key | key in a
    ensures key in b
    ensures a[key] == b[key]
    {
      ghost var i := IndexOfKey(right, key);
      Imaps(right, i);
      Imaps(kvl, i + idx as int);
    }

    forall key | key in b
    ensures key in a
    {
      ghost var i := IndexOfKey(kvl, key);
      Imaps(right, i - idx as int);
      Imaps(kvl, i);
    }

    assert a == b;
  }

  /*function splitKvlInList(buckets: seq<Kvl>, slot: int, pivot: Key)
  : (buckets' : seq<Kvl>)
  requires forall i | 0 <= i < |buckets| :: WF(buckets[i])
  requires 0 <= slot < |buckets|
  ensures |buckets'| == |buckets| + 1

  lemma splitKvlInListCorrect(buckets: seq<Kvl>, slot: int, pivot: Key)
  requires forall i | 0 <= i < |buckets| :: WF(buckets[i])
  requires 0 <= slot < |buckets|
  ensures var buckets' := splitKvlInList(buckets, slot, pivot);
    && |buckets'| == |buckets| + 1
    && (forall i | 0 <= i < |buckets'| :: WF(buckets'[i]))
    && (ISeq(buckets') == SplitBucketInList(ISeq(buckets), slot, pivot))

  method SplitKvlInList(buckets: seq<Kvl>, slot: int, pivot: Key)
  returns (buckets' : seq<Kvl>)
  requires forall i | 0 <= i < |buckets| :: WF(buckets[i])
  requires 0 <= slot < |buckets|
  requires |buckets[slot].keys| < 0x8000_0000_0000_0000
  ensures |buckets'| == |buckets| + 1
  ensures forall i | 0 <= i < |buckets'| :: WF(buckets'[i])
  ensures ISeq(buckets') == SplitBucketInList(ISeq(buckets), slot, pivot)
  ensures buckets' == splitKvlInList(buckets, slot, pivot)
  {
    var l := SplitLeft(buckets[slot], pivot);
    var r := SplitRight(buckets[slot], pivot);
    buckets' := replace1with2(buckets, l, r, slot);
    reveal_SplitBucketInList();
    Ireplace1with2(buckets, l, r, slot);
    assume buckets' == splitKvlInList(buckets, slot, pivot);
  }*/

  /////////////////////////
  //// Joining
  /////////////////////////

  /*function join(kvls: seq<Kvl>) : Kvl
  {
    if |kvls| == 0 then Kvl(PSA.EmptyPsa(), []) else (
      var j := join(DropLast(kvls));
      var l := Last(kvls);
      Kvl(j.keys + l.keys, j.messages + l.messages)
    )
  }

  function LenSum(kvls: seq<Kvl>, i: int) : int
  requires 0 <= i <= |kvls|
  {
    if i == 0 then 0 else LenSum(kvls, i-1) + |kvls[i-1].keys|
  }

  lemma LenSumPrefixLe(kvls: seq<Kvl>, i: int)
  requires 0 <= i <= |kvls|
  ensures LenSum(kvls, i) <= LenSum(kvls, |kvls|)

  decreases |kvls| - i
  {
    if (i < |kvls|) {
      LenSumPrefixLe(kvls, i+1);
    }
  }

  lemma joinEqJoinBucketList(kvls: seq<Kvl>, pivots: seq<Key>)
  requires forall i | 0 <= i < |kvls| :: WF(kvls[i])
  requires WFBucketListProper(ISeq(kvls), pivots)
  ensures WF(join(kvls))
  ensures I(join(kvls)) == JoinBucketList(ISeq(kvls))
  {
    assume false;
  }

  method {:fuel JoinBucketList,0} {:fuel WFBucketList,0}
  Join(kvls: seq<Kvl>, ghost pivots: seq<Key>)
  returns (kvl: Kvl)
  requires forall i | 0 <= i < |kvls| :: WF(kvls[i])
  requires WFBucketListProper(ISeq(kvls), pivots)
  requires |kvls| < 0x8000_0000
  requires forall i | 0 <= i < |kvls| :: |kvls[i].keys| < 0x1_0000_0000
  ensures WF(kvl)
  ensures I(kvl) == JoinBucketList(ISeq(kvls))
  ensures kvl == join(kvls)
  {
    var len: uint64 := 0;
    var i: uint64 := 0;
    while i < |kvls| as uint64
    invariant 0 <= i as int <= |kvls|
    invariant len as int == LenSum(kvls, i as int)
    invariant len <= i * 0x1_0000_0000
    {
      LenSumPrefixLe(kvls, i as int + 1);

      len := len + |kvls[i].keys| as uint64;
      i := i + 1;
    }

    assert kvls == kvls[..i];
    assert len as int == LenSum(kvls, |kvls|);
    var keys := new Key[len];
    var messages := new Message[len];

    var j: uint64 := 0;
    var pos: uint64 := 0;
    while j < |kvls| as uint64
    invariant 0 <= j as int <= |kvls|
    invariant pos as int == LenSum(kvls, j as int)
    invariant 0 <= LenSum(kvls, j as int) <= keys.Length
    invariant keys[..LenSum(kvls, j as int)] == join(kvls[..j]).keys
    invariant messages[..LenSum(kvls, j as int)] == join(kvls[..j]).messages
    {
      LenSumPrefixLe(kvls, j as int + 1);

      assert LenSum(kvls, j as int + 1)
          == LenSum(kvls, j as int) + |kvls[j].keys|
          == pos as int + |kvls[j].keys|;

      assert pos as int + |kvls[j].keys| <= keys.Length;
      NativeArrays.CopySeqIntoArray(kvls[j].keys, 0, keys, pos, |kvls[j].keys| as uint64);
      NativeArrays.CopySeqIntoArray(kvls[j].messages, 0, messages, pos, |kvls[j].messages| as uint64);

      assert pos as int + |kvls[j].keys|
          == LenSum(kvls, j as int) + |kvls[j].keys|
          == LenSum(kvls, j as int + 1);

      assert DropLast(kvls[..j+1]) == kvls[..j];
      assert keys[..LenSum(kvls, j as int + 1)]
          == keys[..pos] + keys[pos .. LenSum(kvls, j as int + 1)]
          == join(kvls[..j]).keys + kvls[j].keys
          == join(kvls[..j+1]).keys;
      assert messages[..LenSum(kvls, j as int + 1)]
          == join(kvls[..j+1]).messages;

      pos := pos + |kvls[j].keys| as uint64;
      j := j + 1;
    }

    kvl := Kvl(keys[..], messages[..]);

    assert keys[..] == keys[..LenSum(kvls, j as int)];
    assert messages[..] == messages[..LenSum(kvls, j as int)];
    assert kvls[..j] == kvls;
    joinEqJoinBucketList(kvls, pivots);
  }*/

  /////////////////////////
  //// Splitting
  /////////////////////////

  /*function method EmptySeq(n: int) : (s : seq<Kvl>)
  requires n >= 0
  ensures |s| == n
  ensures forall i | 0 <= i < n :: WF(s[i])
  ensures forall i | 0 <= i < n :: s[i] == Kvl([],[])
  {
    if n == 0 then [] else EmptySeq(n-1) + [Kvl([],[])]
  }*/

  /*function splitOnPivots(kvl: Kvl, pivots: seq<Key>)
  : (kvls : seq<Kvl>)
  requires WF(kvl)
  requires |pivots| < 0x7fff_ffff_ffff_ffff
  ensures forall i | 0 <= i < |kvls| :: WF(kvls[i])
  ensures ISeq(kvls) == SplitBucketOnPivots(I(kvl), pivots)
  ensures |kvls| == |pivots| + 1

  method SplitOnPivots(kvl: Kvl, pivots: seq<Key>)
  returns (kvls : seq<Kvl>)
  requires WF(kvl)
  requires P.WFPivots(pivots)
  requires |pivots| < 0x7fff_ffff_ffff_ffff
  requires PSA.psaNumStrings(kvl.keys) as int < 0x8000_0000_0000_0000
  ensures forall i | 0 <= i < |kvls| :: WF(kvls[i])
  ensures ISeq(kvls) == SplitBucketOnPivots(I(kvl), pivots)
  ensures kvls == splitOnPivots(kvl, pivots)
  {
    reveal_IMap();
    kvls := Flush(kvl, EmptySeq(|pivots| + 1), pivots);

    forall key | key in I(kvl)
    ensures I(kvl)[key] != IdentityMessage()
    {
      var i := IndexOfKey(kvl, key);
      Imaps(kvl, i);
    }
    LemmaSplitBucketOnPivotsEqAddMessagesToBuckets(I(kvl), pivots, ISeq(EmptySeq(|pivots| + 1)));
    assume kvls == splitOnPivots(kvl, pivots);
  }*/

  method IsWF(kvl: Kvl) returns (b: bool)
  requires PSA.WF(kvl.keys)
  requires forall i | 0 <= i < PSA.psaNumStrings(kvl.keys) :: |PSA.psaElement(kvl.keys, i)| <= MaxLen() as int
  requires PSA.psaNumStrings(kvl.keys) as int < 0x1_0000_0000_0000_0000
  requires |kvl.messages| < 0x1_0000_0000_0000_0000
  requires IsStrictlySorted(PSA.I(kvl.keys))
  requires forall i | 0 <= i < |kvl.messages| :: kvl.messages[i] != IdentityMessage()
  ensures b == WF(kvl)
  {
    if PSA.psaNumStrings(kvl.keys)  != |kvl.messages| as uint64
    {
      assert !WF(kvl);
      return false;
    }

    /*
    reveal_IsStrictlySorted();

    var k: uint64 := 1;
    while k < PSA.psaNumStrings(kvl.keys) 
    invariant PSA.psaNumStrings(kvl.keys) as int > 0 ==> 0 <= k as int <= PSA.psaNumStrings(kvl.keys) as int
    invariant PSA.psaNumStrings(kvl.keys) as int > 0 ==> forall i, j :: 0 <= i < j < k as int ==> lt(PSA.psaElement(kvl.keys, i), kvl.keys[j])
    {
      var c := cmp(kvl.keys[k-1], kvl.keys[k]);
      if (c >= 0) {
        return false;
      }
      k := k + 1;
    }
    */

    assert WF(kvl);
    return true;
  }

  /////////////////////////
  //// Misc utils
  /////////////////////////

  function method {:opaque} Empty() : (kvl : Kvl)
  ensures WF(kvl)
  ensures I(kvl) == B(map[])
  {
    reveal_IMap();
    Kvl(PSA.EmptyPsa(),[])
  }

  lemma Islice(kvls: seq<Kvl>, a: int, b: int)
  requires 0 <= a <= b <= |kvls|
  requires forall i | 0 <= i < |kvls| :: WF(kvls[i])
  ensures forall i | 0 <= i < |kvls[a..b]| :: WF(kvls[a..b][i])
  ensures ISeq(kvls[a..b]) == ISeq(kvls)[a..b]
  {
    reveal_IMap();
    if b == |kvls| {
      if (a == b) {
      } else {
        Islice(DropLast(kvls), a, b - 1);
      }
    } else {
      Islice(DropLast(kvls), a, b);
    }
  }

  lemma Isuffix(kvls: seq<Kvl>, a: int)
  requires 0 <= a <= |kvls|
  requires forall i | 0 <= i < |kvls| :: WF(kvls[i])
  ensures forall i | 0 <= i < |kvls[a..]| :: WF(kvls[a..][i])
  ensures ISeq(kvls[a..]) == ISeq(kvls)[a..]
  {
    Islice(kvls, a, |kvls|);
  }

  lemma IPopFront(kvl: Kvl, kvls: seq<Kvl>)
  requires WF(kvl)
  requires forall i | 0 <= i < |kvls| :: WF(kvls[i])
  ensures ISeq([kvl] + kvls) == [I(kvl)] + ISeq(kvls)
  {
    if |kvls| == 0 {
    } else {
      IPopFront(kvl, DropLast(kvls));
    }
  }

  lemma IPopBack(kvls: seq<Kvl>, kvl: Kvl)
  requires WF(kvl)
  requires forall i | 0 <= i < |kvls| :: WF(kvls[i])
  ensures ISeq(kvls + [kvl]) == ISeq(kvls) + [I(kvl)]
  {
    reveal_ISeq();
  }

  lemma Ireplace1with2(kvls: seq<Kvl>, kvl1: Kvl, kvl2: Kvl, slot: int)
  requires WF(kvl1)
  requires WF(kvl2)
  requires 0 <= slot < |kvls|
  requires forall i | 0 <= i < |kvls| :: WF(kvls[i])
  ensures forall i | 0 <= i < |replace1with2(kvls, kvl1, kvl2, slot)| :: WF(replace1with2(kvls, kvl1, kvl2, slot)[i])
  ensures ISeq(replace1with2(kvls, kvl1, kvl2, slot)) == replace1with2(ISeq(kvls), I(kvl1), I(kvl2), slot)
  {
    forall i | 0 <= i < |replace1with2(kvls, kvl1, kvl2, slot)|
    ensures WF(replace1with2(kvls, kvl1, kvl2, slot)[i])
    {
      if i < slot {
        assert replace1with2(kvls, kvl1, kvl2, slot)[i] == kvls[i];
      }
      if i == slot {
        assert replace1with2(kvls, kvl1, kvl2, slot)[i] == kvl1;
      }
      if i == slot + 1 {
        assert replace1with2(kvls, kvl1, kvl2, slot)[i] == kvl2;
      }
      if i > slot + 1 {
        assert replace1with2(kvls, kvl1, kvl2, slot)[i] == kvls[i-1];
      }
    }

    if slot == |kvls|-1 {
    } else {
      Ireplace1with2(DropLast(kvls), kvl1, kvl2, slot);
    }

    reveal_replace1with2();
  }

  /////////////////////////
  //// Weight stuff
  /////////////////////////

  function WeightKvl(kvl: Kvl) : int
    requires PSA.WF(kvl.keys)
    requires forall i | 0 <= i < PSA.psaNumStrings(kvl.keys) :: |PSA.psaElement(kvl.keys, i)| <= MaxLen() as int
  {
    var ikeys := PSA.I(kvl.keys);
    WeightKeySeq(PSA.I(kvl.keys)) + WeightMessageSeq(kvl.messages)
  }

  function WeightKvlSeq(kvls: seq<Kvl>) : int
    requires forall i | 0 <= i < |kvls| :: PSA.WF(kvls[i].keys)
    requires forall j, i | 0 <= j < |kvls| && 0 <= i < PSA.psaNumStrings(kvls[j].keys) :: |PSA.psaElement(kvls[j].keys, i)| <= MaxLen() as int
  {
    if |kvls| == 0 then 0 else WeightKvlSeq(DropLast(kvls)) + WeightKvl(Last(kvls))
  }

  lemma IKeys(kvl: Kvl)
    requires WF(kvl)
    ensures I(kvl).b.Keys <= Set(PSA.I(kvl.keys))
    decreases PSA.psaNumStrings(kvl.keys);
  {
    var ikeys := PSA.I(kvl.keys);
    var ikvl := IMap(kvl);
    
    if |ikeys| == 0 {
    } else {
      var prekvl := prefix(kvl, |ikeys|-1);
      WFPrefix(kvl, |ikeys|-1);
      assert prekvl == Kvl(PSA.psaDropLast(kvl.keys), DropLast(kvl.messages));
      var lastkey: Key := Last(ikeys);
      var lastmessage := Last(kvl.messages);
      reveal_IMap();
      assert ikvl == IMap(prekvl)[lastkey := lastmessage];
      IKeys(prekvl);
    }
  }
  
  lemma LastLargerThanPrefix(kvl: Kvl)
    requires WF(kvl)
    requires 0 < PSA.psaNumStrings(kvl.keys)
    ensures forall k | k in I(prefix(kvl, PSA.psaNumStrings(kvl.keys) as int - 1)).b :: lt(k, PSA.LastElement(kvl.keys))
    decreases PSA.psaNumStrings(kvl.keys);
  {
    var prekvl := Kvl(PSA.psaDropLast(kvl.keys), DropLast(kvl.messages));
    WFPrefix(kvl, PSA.psaNumStrings(kvl.keys) as int -1);
    var b := I(prekvl).b;

    var last := PSA.LastElement(kvl.keys);
    if PSA.psaNumStrings(prekvl.keys) == 0 {
    } else {
      var prelast := PSA.LastElement(prekvl.keys);
      LastLargerThanPrefix(prekvl);
      var ikeys := PSA.I(kvl.keys);
      assert last == Last(ikeys);
      assert prelast == ikeys[|ikeys|-2];
      IsStrictlySortedImpliesLt(ikeys, |ikeys|-2, |ikeys|-1);
      forall k | k in b
        ensures lt(k, last)
      {
        IKeys(prekvl);
        var i :| 0 <= i < |ikeys|-1 && k == ikeys[i];
        IsStrictlySortedImpliesLte(ikeys, i, |ikeys|-2);
      }
    }
  }

  lemma LastNotInPrefix(kvl: Kvl)
    requires WF(kvl)
    requires 0 < PSA.psaNumStrings(kvl.keys)
    ensures PSA.LastElement(kvl.keys) !in I(prefix(kvl, PSA.psaNumStrings(kvl.keys) as int - 1)).b
  {
    LastLargerThanPrefix(kvl);
    var last := PSA.LastElement(kvl.keys);
    var pre := I(prefix(kvl, PSA.psaNumStrings(kvl.keys) as int - 1)).b;
    forall k | k in pre
      ensures last != k
    {
      assert lt(k, last);
    }
  }
  
  lemma kvlWeightEq(kvl: Kvl)
  requires WF(kvl)
  ensures WeightKvl(kvl) == WeightBucket(I(kvl))
  decreases PSA.psaNumStrings(kvl.keys) as int
  {
    reveal_IMap();
    if PSA.psaNumStrings(kvl.keys) as int == 0 {
      WeightBucketEmpty();
    } else {
      WFPrefix(kvl, PSA.psaNumStrings(kvl.keys) as int - 1);
      kvlWeightEq(Kvl(PSA.psaDropLast(kvl.keys), DropLast(kvl.messages)));
      if PSA.LastElement(kvl.keys) in IMap(Kvl(PSA.psaDropLast(kvl.keys), DropLast(kvl.messages))) {
        var i := IndexOfKey(Kvl(PSA.psaDropLast(kvl.keys), DropLast(kvl.messages)), PSA.LastElement(kvl.keys));
        reveal_IsStrictlySorted();
      }
      LastNotInPrefix(kvl);
      WeightBucketInduct(I(Kvl(PSA.psaDropLast(kvl.keys), DropLast(kvl.messages))), PSA.LastElement(kvl.keys), Last(kvl.messages));
      assert WeightKvl(kvl)
          == WeightKvl(Kvl(PSA.psaDropLast(kvl.keys), DropLast(kvl.messages)))
              + WeightKey(PSA.LastElement(kvl.keys)) + WeightMessage(Last(kvl.messages))
          == WeightBucket(I(Kvl(PSA.psaDropLast(kvl.keys), DropLast(kvl.messages))))
              + WeightKey(PSA.LastElement(kvl.keys)) + WeightMessage(Last(kvl.messages));
    }
  }

  lemma kvlSeqWeightEq(kvls: seq<Kvl>)
  requires forall i | 0 <= i < |kvls| :: WF(kvls[i])
  ensures WeightKvlSeq(kvls) == WeightBucketList(ISeq(kvls))
  {
    reveal_WeightBucketList();
    if |kvls| == 0 {
    } else {
      kvlSeqWeightEq(DropLast(kvls));
      Islice(kvls, 0, |kvls| - 1);
      kvlWeightEq(Last(kvls));
    }
  }

  lemma kvlWeightPrefixLe(kvl: Kvl, j: int)
  requires WF(kvl)
  requires 0 <= j <= PSA.psaNumStrings(kvl.keys) as int
  ensures WF(prefix(kvl, j))
  ensures WeightKvl(prefix(kvl, j)) <= WeightKvl(kvl);
  decreases PSA.psaNumStrings(kvl.keys) as int
  {
    if j == PSA.psaNumStrings(kvl.keys) as int {
      assert prefix(kvl, j) == kvl;
    } else {
      WFPrefix(kvl, PSA.psaNumStrings(kvl.keys) as int - 1);
      kvlWeightPrefixLe(Kvl(PSA.psaDropLast(kvl.keys), DropLast(kvl.messages)), j);
      assert prefix(kvl, j) == prefix(Kvl(PSA.psaDropLast(kvl.keys), DropLast(kvl.messages)), j);
      assert WeightKvl(prefix(kvl, j))
          == WeightKvl(prefix(Kvl(PSA.psaDropLast(kvl.keys), DropLast(kvl.messages)), j))
          <= WeightKvl(Kvl(PSA.psaDropLast(kvl.keys), DropLast(kvl.messages)))
          <= WeightKvl(kvl);
    }
  }

  lemma lenKeysLeWeightOver4(kvl: Kvl)
  requires WF(kvl)
  ensures 4*PSA.psaNumStrings(kvl.keys) as int <= WeightBucket(I(kvl))
  decreases PSA.psaNumStrings(kvl.keys) as int
  {
    if PSA.psaNumStrings(kvl.keys) as int == 0 {
    } else {
      WFPrefix(kvl, PSA.psaNumStrings(kvl.keys) as int - 1);
      lenKeysLeWeightOver4(Kvl(PSA.psaDropLast(kvl.keys), DropLast(kvl.messages)));
      kvlWeightEq(kvl);
      kvlWeightEq(Kvl(PSA.psaDropLast(kvl.keys), DropLast(kvl.messages)));
    }
  }

  // This is far weaker than it could be, but it's probably good enough.
  // Weight is on the order of a few million, and I plan on using this lemma
  // to show that numbers fit within 64 bits.
  lemma lenKeysLeWeight(kvl: Kvl)
  requires WF(kvl)
  ensures PSA.psaNumStrings(kvl.keys) as int <= WeightBucket(I(kvl))
  {
    lenKeysLeWeightOver4(kvl);
  }

  lemma WeightKvlInduct(kvl: Kvl, j: int)
  requires WF(kvl)
  requires 0 <= j < PSA.psaNumStrings(kvl.keys) as int
  ensures WF(prefix(kvl, j as int))
  ensures WF(prefix(kvl, j as int + 1))
  ensures WeightKvl(prefix(kvl, j as int)) +
      WeightKey(PSA.psaElement(kvl.keys, j as uint64)) + WeightMessage(kvl.messages[j])
          == WeightKvl(prefix(kvl, j as int + 1));
  {
    WFPrefix(kvl, j as int);
    WFPrefix(kvl, j as int + 1);
    assert DropLast(prefix(kvl, j as int + 1).messages)
        == prefix(kvl, j as int).messages;
    assert PSA.psaDropLast(prefix(kvl, j as int + 1).keys)
        == prefix(kvl, j as int).keys;
  }

  method computeWeightKvl(kvl: Kvl)
  returns (weight: uint64)
  requires WF(kvl)
  requires WeightBucket(I(kvl)) < 0x1_0000_0000_0000_0000
  ensures weight as int == WeightBucket(I(kvl))
  {
    kvlWeightEq(kvl);
    lenKeysLeWeight(kvl);

    forall j | 0 <= j <= PSA.psaNumStrings(kvl.keys) as int
      ensures WF(prefix(kvl, j as int))
    {
      WFPrefix(kvl, j as int);
    }
    
    var j: uint64 := 0;
    var w: uint64 := 0;
    while j < PSA.psaNumStrings(kvl.keys) 
    invariant 0 <= j as int <= PSA.psaNumStrings(kvl.keys) as int
    invariant w as int == WeightKvl(prefix(kvl, j as int))
    {
      WeightKvlInduct(kvl, j as int);
      kvlWeightPrefixLe(kvl, j as int + 1);

      w := w + WeightKeyUint64(PSA.psaElement(kvl.keys, j)) + WeightMessageUint64(kvl.messages[j]);
      j := j + 1;
    }
    weight := w;

    assert prefix(kvl, PSA.psaNumStrings(kvl.keys) as int) == kvl;
  }

  function toKvlInternal(bucket: Bucket) : (kvl: Kvl)
  requires WFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  requires |bucket.keys| < 0x1_0000_0000 - 1
  requires MaxLen() as int * |bucket.keys| < 0x1_0000_0000 
  {
    PSA.psaCanAppendSeqHelper2(PSA.EmptyPsa(), bucket.keys, MaxLen() as int);
    Kvl(PSA.psaFromSeq(bucket.keys), bucket.msgs)
  }

  lemma toKvlCorrect(bucket: Bucket)
  requires WFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  requires |bucket.keys| < 0x1_0000_0000 - 1
  requires MaxLen() as int * |bucket.keys| < 0x1_0000_0000 
  ensures WF(toKvlInternal(bucket))
  ensures I(toKvlInternal(bucket)) == bucket
  {
    PSA.psaCanAppendSeqHelper2(PSA.EmptyPsa(), bucket.keys, MaxLen() as int);
    var keys := PSA.psaFromSeq(bucket.keys);
    var kvl := toKvlInternal(bucket);
    forall i | 0 <= i < PSA.psaNumStrings(keys)
      ensures |PSA.psaElement(keys, i)| <= MaxLen() as int
    {
      assert PSA.psaElement(keys, i) == PSA.I(keys)[i];
    }
    reveal_WFBucket();
    assert forall i | 0 <= i < |bucket.msgs| :: bucket.msgs[i] != IdentityMessage();
  }
  
  function {:opaque} toKvl(bucket: Bucket) : (kvl: Kvl)
  requires WFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  requires |bucket.keys| < 0x1_0000_0000 - 1
  requires MaxLen() as int * |bucket.keys| < 0x1_0000_0000 
  ensures WF(kvl)
  ensures I(kvl) == bucket
  {
    toKvlCorrect(bucket);
    toKvlInternal(bucket)
  }

  function {:opaque} toKvlSeq(buckets: BucketList) : (kvls: seq<Kvl>)
  requires BucketListWellMarshalled(buckets)
  requires forall i | 0 <= i < |buckets| :: WFBucket(buckets[i])
  ensures |kvls| == |buckets|
  ensures forall i | 0 <= i < |kvls| :: WF(kvls[i])
  ensures ISeq(kvls) == buckets
  {
    if |buckets| == 0 then (
      []
    ) else (
      toKvlSeq(DropLast(buckets)) + [toKvl(Last(buckets))]
    )
  }

  // Dafny type inference can't figure out the type of the naked
  // maximumOpt call, so we wrap it
  function KeySetMax(keys: set<seq<byte>>) : seq<byte>
    requires keys != {}
    requires forall k | k in keys :: |k| <= MaxLen() as int
  {
    var v: Option<seq<byte>> := maximumOpt(keys);
    v.value
  }
    
  
  lemma lastIsMax(kvl: Kvl)
  requires WF(kvl)
  requires 0 < PSA.psaNumStrings(kvl.keys) as int
  ensures I(kvl).b.Keys != {}
  ensures KeySetMax(I(kvl).b.Keys) == PSA.LastElement(kvl.keys)
  {
    Imaps(kvl, PSA.psaNumStrings(kvl.keys) as int - 1);
    assert PSA.LastElement(kvl.keys) in IMap(kvl).Keys;
    LastLargerThanPrefix(kvl);
    var ikeys := PSA.I(kvl.keys);
    var last := PSA.LastElement(kvl.keys);
    assert last == Last(ikeys);
    forall key | key in IMap(kvl).Keys
    ensures lte(key, PSA.LastElement(kvl.keys))
    {
      var i := IndexOfKey(kvl, key);
      assert ikeys[i] == key;
      IsStrictlySortedImpliesLte(ikeys, i, |ikeys|-1);
    }
  }

  lemma lastIsNotInDropLast(kvl: Kvl)
  requires WF(kvl)
  requires PSA.psaNumStrings(kvl.keys) as int > 0
  ensures WF(Kvl(PSA.psaDropLast(kvl.keys), DropLast(kvl.messages)))
  ensures PSA.LastElement(kvl.keys) !in IMap(Kvl(PSA.psaDropLast(kvl.keys), DropLast(kvl.messages)));
  {
    WFPrefix(kvl, PSA.psaNumStrings(kvl.keys) as int - 1);
    LastNotInPrefix(kvl);
  }

  lemma I_injective(kvl1: Kvl, kvl2: Kvl)
  requires WF(kvl1)
  requires WF(kvl2)
  requires IMap(kvl1) == IMap(kvl2)
  ensures kvl1 == kvl2
  decreases PSA.psaNumStrings(kvl1.keys) as int
  {
    reveal_IMap();
    reveal_IsStrictlySorted();
    if PSA.psaNumStrings(kvl1.keys) as int == 0 {
    } else {
      lastIsMax(kvl1);
      lastIsMax(kvl2);
      ghost var max1: Option<seq<byte>> := maximumOpt(IMap(kvl1).Keys);
      ghost var max2: Option<seq<byte>> := maximumOpt(IMap(kvl2).Keys);
      assert Some(PSA.LastElement(kvl1.keys))
          == max1
          == max2
          == Some(PSA.LastElement(kvl2.keys));

      var key := PSA.LastElement(kvl1.keys);
      assert key == PSA.LastElement(kvl2.keys);
      lastIsNotInDropLast(kvl1);
      lastIsNotInDropLast(kvl2);
      //assert key !in IMap(Kvl(DropLast(kvl1.keys), DropLast(kvl1.messages)));
      //assert key !in IMap(Kvl(DropLast(kvl2.keys), DropLast(kvl2.messages)));
      assert IMap(Kvl(PSA.psaDropLast(kvl1.keys), DropLast(kvl1.messages)))
          == MapRemove1(IMap(kvl1), key)
          == MapRemove1(IMap(kvl2), key)
          == IMap(Kvl(PSA.psaDropLast(kvl2.keys), DropLast(kvl2.messages)));
      I_injective(
        prefix(kvl1, PSA.psaNumStrings(kvl1.keys) as int - 1),
        prefix(kvl2, PSA.psaNumStrings(kvl2.keys) as int - 1));
      assert Last(kvl1.messages) == Last(kvl2.messages);
    }
  }

  lemma toKvlI_eq(kvl: Kvl)
  requires WF(kvl)
  ensures WFBucket(I(kvl))
  ensures toKvl(I(kvl)) == kvl
  {
    WFImpliesWFBucket(kvl);
    assert I(toKvl(I(kvl))) == I(kvl);
    I_injective(toKvl(I(kvl)), kvl);
  }

  lemma WFPivotsOfGetMiddleKey(bucket: Bucket)
  requires WFBucket(bucket)
  ensures P.WFPivots([getMiddleKey(bucket)])
  {
    reveal_IsStrictlySorted();
    SeqComparison.reveal_lte();
    IsNotMinimum([], getMiddleKey(bucket));
  }
}
