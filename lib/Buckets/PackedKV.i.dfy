include "PackedStringArray.i.dfy"
include "BucketsLib.i.dfy"
include "BucketModel.i.dfy"

module PackedKV {
  import PSA = PackedStringArray
  import opened NativeTypes
  import KeyspaceImpl = Lexicographic_Byte_Order_Impl
  import Keyspace = KeyspaceImpl.Ord
  import opened KeyType
  import opened ValueType`Internal
  import opened ValueMessage`Internal
  import opened BucketsLib
  import opened Options
  import opened Sequences
  import opened Maps
  import Integer_Order
  
  datatype Pkv = Pkv(
      keys: PSA.Psa,
      messages: PSA.Psa)

  // TODO(robj): Ideally these constraints would be moved out of this
  // "pure" data structure.
  predicate ValidKeyByteString(s: seq<byte>)
  {
    |s| <= KeyType.MaxLen() as int
  }

  predicate ValidStringLens<A>(strs: seq<seq<A>>, upper_bound: nat)
  {
    forall i | 0 <= i < |strs| :: |strs[i]| <= upper_bound
  }

  predicate ValidKeyLens<A>(strs: seq<seq<A>>)
  {
    ValidStringLens(strs, KeyType.MaxLen() as nat)
  }

  function IKeys(psa: PSA.Psa) : (res : seq<Key>)
  requires PSA.WF(psa)
  requires ValidStringLens(PSA.I(psa), KeyType.MaxLen() as nat)
  {
    PSA.I(psa)
  }

  function {:opaque} psaSeq_Messages(psa: PSA.Psa, i: int) : (res : seq<Message>)
  requires PSA.WF(psa)
  requires 0 <= i <= |psa.offsets|
  ensures |res| == i
  ensures forall j | 0 <= j < i :: res[j] == bytestring_to_Message(PSA.psaElement(psa, j as uint64))
  {
    if i == 0 then [] else psaSeq_Messages(psa, i-1) + [
        bytestring_to_Message(PSA.psaElement(psa, (i-1) as uint64))]
  }

  function IMessages(psa: PSA.Psa) : (res : seq<Message>)
  requires PSA.WF(psa)
  {
    psaSeq_Messages(psa, |psa.offsets|)
  }

  lemma DefineIMessage(psa: PSA.Psa, j: int)
    requires PSA.WF(psa)
    requires ValidMessageBytestrings(PSA.I(psa))
    requires 0 <= j < |psa.offsets|
    ensures |PSA.psaElement(psa, j as uint64)| <= ValueType.MaxLen() as nat
    ensures IMessages(psa)[j] == Define(PSA.psaElement(psa, j as uint64))
  {
    assert |PSA.I(psa)[j]| == |PSA.psaElement(psa, j as uint64)|;
  }

  predicate WF(pkv: Pkv) {
    && PSA.WF(pkv.keys)
    && PSA.WF(pkv.messages)
    && |pkv.keys.offsets| == |pkv.messages.offsets|
    && ValidKeyLens(PSA.I(pkv.keys))
    && ValidMessageBytestrings(PSA.I(pkv.messages))
    && IdentityMessage() !in IMessages(pkv.messages)
  }

  function IMap(pkv: Pkv) : (bucket : BucketMap)
  requires WF(pkv)
  ensures WFBucketMap(bucket)
  {
    assert IdentityMessage() !in Set(IMessages(pkv.messages));
    BucketMapOfSeq(IKeys(pkv.keys), IMessages(pkv.messages))
  }

  predicate SortedKeys(pkv: Pkv)
  requires WF(pkv)
  {
    Keyspace.IsStrictlySorted(IKeys(pkv.keys))
  }

  function I(pkv: Pkv) : (bucket : Bucket)
  requires WF(pkv)
  ensures WFBucket(bucket)
  {
    // Note that this might not be WellMarshalled
    BucketMapWithSeq(IMap(pkv), IKeys(pkv.keys), IMessages(pkv.messages))
  }

  function method EmptyPkv() : (result: Pkv)
    ensures WF(result)
    ensures IMap(result) == map[]
  {
    Pkv(PSA.EmptyPsa(), PSA.EmptyPsa())
  }

  function method NumKVPairs(pkv: Pkv) : uint64
    requires WF(pkv)
  {
    PSA.psaNumStrings(pkv.keys)
  }
  
  method ComputeValidStringLens(psa: PSA.Psa, upper_bound: uint64)
  returns (b: bool)
  requires PSA.WF(psa)
  ensures b == ValidStringLens(PSA.I(psa), upper_bound as nat)
  {
    var i: uint64 := 0;

    while i < PSA.psaNumStrings(psa)
      invariant i <= PSA.psaNumStrings(psa)
      invariant forall j | 0 <= j < i :: |PSA.I(psa)[j]| <= upper_bound as nat
    {
      assert |PSA.I(psa)[i]| == PSA.psaEnd(psa, i) as nat - PSA.psaStart(psa, i) as nat;
      if upper_bound < PSA.psaEnd(psa, i) as uint64 - PSA.psaStart(psa, i) as uint64 {
        b := false;
        return;
      }
      i := i + 1;
    }
    
    return true;
  }

  method ComputeIsSorted(pkv: Pkv)
    returns (b: bool)
    requires PSA.WF(pkv.keys)
    ensures b == Keyspace.IsStrictlySorted(PSA.I(pkv.keys))
  {
    ghost var ikeys := PSA.I(pkv.keys);
    
    Keyspace.reveal_IsStrictlySorted();

    if |pkv.keys.offsets| <= 1 {
      return true;
    }
    
    var i: uint64 := 0;
    while i < |pkv.keys.offsets| as uint64 - 1
      invariant i as int <= |pkv.keys.offsets| - 1
      invariant Keyspace.IsStrictlySorted(ikeys[..i+1])
    {
      var c := KeyspaceImpl.cmp(PSA.psaElement(pkv.keys, i), PSA.psaElement(pkv.keys, i+1));
      if c >= 0 {
        assert PSA.I(pkv.keys)[i] == PSA.psaElement(pkv.keys, i);
        assert PSA.I(pkv.keys)[i+1] == PSA.psaElement(pkv.keys, i+1);
        return false;
      }
      Keyspace.StrictlySortedAugment(ikeys[..i+1], ikeys[i+1]);
      assert ikeys[..i+2] == ikeys[..i+1] + [ikeys[i+1]];
      i := i + 1;
    }
    
    assert ikeys == ikeys[..i+1];
      
    return true;
  }

  function SizeOfPkv(pkv: Pkv) : int
  {
    PSA.SizeOfPsa(pkv.keys) + PSA.SizeOfPsa(pkv.messages)
  }

  function method SizeOfPkvUint64(pkv: Pkv) : uint64
  requires WF(pkv)
  {
    PSA.SizeOfPsaUint64(pkv.keys) + PSA.SizeOfPsaUint64(pkv.messages)
  }

  function method WeightPkv(pkv: Pkv) : uint64
  requires WF(pkv)
  {
    4 * |pkv.keys.offsets| as uint64 + |pkv.keys.data| as uint64 +
    4 * |pkv.messages.offsets| as uint64 + |pkv.messages.data| as uint64
  }

  function method FirstKey(pkv: Pkv) : Key
  requires WF(pkv)
  requires |pkv.keys.offsets| > 0
  {
    assert PSA.FirstElement(pkv.keys) == PSA.I(pkv.keys)[0];
    PSA.FirstElement(pkv.keys)
  }

  function method LastKey(pkv: Pkv) : Key
  requires WF(pkv)
  requires |pkv.keys.offsets| > 0
  {
    assert PSA.LastElement(pkv.keys) == Last(PSA.I(pkv.keys));
    PSA.LastElement(pkv.keys)
  }

  function method GetKey(pkv: Pkv, i: uint64) : Key
  requires WF(pkv)
  requires 0 <= i as int < |pkv.keys.offsets|
  {
    assert PSA.psaElement(pkv.keys, i) == PSA.I(pkv.keys)[i];
    PSA.psaElement(pkv.keys, i)
  }

  function method GetMessage(pkv: Pkv, i: uint64) : Message
  requires WF(pkv)
  requires 0 <= i as int < |pkv.messages.offsets|
  {
    bytestring_to_Message(PSA.psaElement(pkv.messages, i))
  }

  function binarySearchPostProc(lo: nat, sub: Option<nat>) : Option<nat>
  {
    if sub.Some? then
      Some(lo + sub.value)
    else
      None
  }

  method BinarySearchQuery(pkv: Pkv, key: Key)
  returns (msg: Option<Message>)
  requires WF(pkv)
  ensures msg == bucketBinarySearchLookup(I(pkv), key)
  {
    ghost var keys := I(pkv).keys;
    
    var lo: uint64 := 0;
    var hi: uint64 := |pkv.keys.offsets| as uint64;

    assert keys == keys[lo..hi];
    
    while lo < hi
      invariant lo <= hi <= |pkv.keys.offsets| as uint64
      invariant binarySearch(keys, key) == binarySearchPostProc(lo as nat, binarySearch(keys[lo..hi], key))
    {
      var mid: uint64 := (lo + hi) / 2;
      var c := KeyspaceImpl.cmp(key, GetKey(pkv, mid));
      if c == 0 {
        msg := Some(GetMessage(pkv, mid));
        return;
      } else if (c < 0) {
        ghost var rkeys := keys[lo..hi];
        ghost var rmid := |rkeys| / 2;
        hi := mid;
        assert keys[lo..hi] == rkeys[..rmid];
      } else {
        lo := mid + 1;
      }
    }

    msg := None;
  }

  predicate canAppend(pkv: Pkv, key: Key, msg: seq<byte>)
    requires WF(pkv)
  {
    && PSA.psaCanAppend(pkv.keys, key)
    && PSA.psaCanAppend(pkv.messages, msg)
    && ValidMessageBytestring(msg)
  }

  function AppendEncodedMessage(pkv: Pkv, key: Key, msg: seq<byte>) : (result: Pkv)
    requires WF(pkv)
    requires canAppend(pkv, key, msg)
    ensures WF(result)
    ensures IKeys(result.keys) == IKeys(pkv.keys) + [ key ]
  {
    PSA.psaAppendIAppend(pkv.keys, key);
    PSA.psaAppendIAppend(pkv.messages, msg);
    Pkv(PSA.psaAppend(pkv.keys, key), PSA.psaAppend(pkv.messages, msg))
  }
  
  function Append(pkv: Pkv, key: Key, msg: Message) : (result: Pkv)
    requires WF(pkv)
    requires msg.Define?
    requires canAppend(pkv, key, Message_to_bytestring(msg))
    ensures WF(result)
  {
    AppendEncodedMessage(pkv, key, Message_to_bytestring(msg))
  }

//~  lemma IMapAppend(pkv: Pkv, key: Key, msg: seq<byte>)
//~    requires WF(pkv)
//~    requires canAppend(pkv, key, msg)
//~    ensures IMap(AppendEncodedMessage(pkv, key, msg)) == IMap(pkv)[key := bytestring_to_Message(msg)]
//~  {
//~    PSA.psaAppendIAppend(pkv.keys, key);
//~    PSA.psaAppendIAppend(pkv.messages, msg);
//~    var keys := PSA.I(pkv.keys);
//~    var messages := IMessages(pkv.messages);
//~    var newpkv := AppendEncodedMessage(pkv, key, msg);
//~    var newkeys := PSA.I(newpkv.keys);
//~    var newmessages := IMessages(newpkv.messages);
//~
//~    assert forall i | 0 <= i < |messages| :: Sequences.DropLast(newmessages)[i] == bytestring_to_Message(PSA.I(newpkv.messages)[i]);
//~    assert Sequences.DropLast(newmessages) == messages;
//~    assert Last(newmessages) == bytestring_to_Message(msg);
//~
//~    calc {
//~      IMap(newpkv);
//~      { reveal_BucketMapOfSeq(); }
//~      BucketMapOfSeq(keys, messages)[key := bytestring_to_Message(msg)];
//~      { reveal_BucketMapOfSeq(); }
//~      IMap(pkv)[key := bytestring_to_Message(msg)];
//~    }
//~  }

  function subPkv(pkv: Pkv, from: uint64, to: uint64) : (result: Pkv)
    requires WF(pkv)
    requires 0 <= from <= to <= PSA.psaNumStrings(pkv.keys)
    ensures WF(result)
    ensures BucketWellMarshalled(I(pkv)) ==> BucketWellMarshalled(I(result))
  {
    if BucketWellMarshalled(I(pkv)) then
      Keyspace.StrictlySortedSubsequence(PSA.I(pkv.keys), from as int, to as int);
      Pkv(PSA.psaSubSeq(pkv.keys, from, to), PSA.psaSubSeq(pkv.messages, from, to))
    else 
      Pkv(PSA.psaSubSeq(pkv.keys, from, to), PSA.psaSubSeq(pkv.messages, from, to))
  }

  method SubPkv(pkv: Pkv, from: uint64, to: uint64) returns (result: Pkv)
    requires WF(pkv)
    requires 0 <= from <= to <= PSA.psaNumStrings(pkv.keys)
    ensures result == subPkv(pkv, from, to)
  {
    var subkeys := PSA.PsaSubSeq(pkv.keys, from, to);
    var submessages := PSA.PsaSubSeq(pkv.messages, from, to);
    result := Pkv(subkeys, submessages);
  }
  
  function DropLast(pkv: Pkv) : (result: Pkv)
    requires WF(pkv)
    requires 0 < NumKVPairs(pkv)
    ensures WF(result)
  {
    subPkv(pkv, 0, NumKVPairs(pkv) - 1)
  }

  lemma Imaps(pkv: Pkv, i: int)
    requires WF(pkv)
    requires Keyspace.IsStrictlySorted(PSA.I(pkv.keys))
    requires 0 <= i < |PSA.I(pkv.keys)|
    ensures MapsTo(IMap(pkv), PSA.I(pkv.keys)[i], bytestring_to_Message(PSA.I(pkv.messages)[i]))
    decreases |PSA.I(pkv.keys)|
  {
    var ikeys := PSA.I(pkv.keys);
    var imessages := PSA.I(pkv.messages);
    
    if (i == |ikeys| - 1) {
      reveal_BucketMapOfSeq();
    } else {
      Keyspace.reveal_IsStrictlySorted();
      reveal_BucketMapOfSeq();
      Imaps(DropLast(pkv), i);
      forall j | 0 <= j < |Sequences.DropLast(IMessages(pkv.messages))|
        ensures Sequences.DropLast(IMessages(pkv.messages))[j] == IMessages(PSA.psaDropLast(pkv.messages))[j]
      {
        calc {
          Sequences.DropLast(IMessages(pkv.messages))[j];
          bytestring_to_Message(PSA.I(pkv.messages)[j]);
        }
      }
      assert Sequences.DropLast(IMessages(pkv.messages)) == IMessages(PSA.psaDropLast(pkv.messages));
    }
  }

  method SplitLeft(pkv: Pkv, pivot: Key) returns (result: Pkv)
    requires WF(pkv)
    requires Keyspace.IsStrictlySorted(PSA.I(pkv.keys))
    ensures WF(result)
    ensures Keyspace.IsStrictlySorted(PSA.I(result.keys))
    ensures I(result) == SplitBucketLeft(I(pkv), pivot)
  {
    var idx := PSA.IndexOfFirstKeyGte(pkv.keys, pivot);
    result := SubPkv(pkv, 0, idx);

    ghost var ikeys := PSA.I(pkv.keys);
    ghost var subkeys := PSA.I(result.keys);
    
    Keyspace.StrictlySortedSubsequence(ikeys, 0, idx as int);
    
    ghost var a := IMap(result);
    ghost var b := SplitBucketLeft(I(pkv), pivot).b;

    forall key | key in a
      ensures MapsTo(b, key, a[key])
    {
      var i := Sequences.IndexOf(ikeys, key);
      Imaps(pkv, i);
      Imaps(result, i);
      reveal_SplitBucketLeft();
    }

    forall key | key in b
      ensures key in a
    {
      reveal_SplitBucketLeft();
    }

    ghost var iresult := I(result);
    ghost var isplit := SplitBucketLeft(I(pkv), pivot);
    WellMarshalledBucketsEq(iresult, isplit);
  }
    
  method SplitRight(pkv: Pkv, pivot: Key) returns (result: Pkv)
    requires WF(pkv)
    requires Keyspace.IsStrictlySorted(PSA.I(pkv.keys))
    ensures WF(result)
    ensures Keyspace.IsStrictlySorted(PSA.I(result.keys))
    ensures I(result) == SplitBucketRight(I(pkv), pivot)
  {
    var idx := PSA.IndexOfFirstKeyGte(pkv.keys, pivot);
    result := SubPkv(pkv, idx, NumKVPairs(pkv));

    ghost var ikeys := PSA.I(pkv.keys);
    ghost var subkeys := PSA.I(result.keys);
    
    Keyspace.StrictlySortedSubsequence(ikeys, idx as int, |ikeys|);
    
    ghost var a := IMap(result);
    ghost var b := SplitBucketRight(I(pkv), pivot).b;

    forall key | key in a
      ensures MapsTo(b, key, a[key])
    {
      var i := Sequences.IndexOf(ikeys, key);
      Imaps(pkv, i);
      Imaps(result, i - idx as int);
      reveal_SplitBucketRight();
    }

    forall key | key in b
      ensures key in a
    {
      reveal_SplitBucketRight();
    }

    ghost var iresult := I(result);
    ghost var isplit := SplitBucketRight(I(pkv), pivot);
    WellMarshalledBucketsEq(iresult, isplit);
  }

  lemma psaTotalLengthBound(psa: PSA.Psa, maxlen: nat)
    requires PSA.WF(psa)
    requires forall i | 0 <= i < |PSA.I(psa)| :: |PSA.I(psa)[i]| <= maxlen
    ensures PSA.psaTotalLength(psa) as nat <= PSA.psaNumStrings(psa) as nat * maxlen
    decreases PSA.psaNumStrings(psa)
  {
    var ipsa := PSA.I(psa);
    if |ipsa| == 0 {
    } else {
      var prepsa := PSA.psaDropLast(psa);
      psaTotalLengthBound(prepsa, maxlen);
      PSA.psaAppendTotalLength(prepsa, Last(ipsa));
    }
  }
  
  function pivotIndexes(keys: seq<Key>, pivots: seq<Key>) : (result: seq<nat>)
    requires Keyspace.IsStrictlySorted(keys)
    ensures |result| == |pivots|
    ensures forall i | 0 <= i < |result| :: result[i] == Keyspace.IndexOfFirstGte(keys, pivots[i])
  {
    if |pivots| == 0 then
      []
    else
      pivotIndexes(keys, Sequences.DropLast(pivots)) + [ Keyspace.IndexOfFirstGte(keys, Last(pivots)) ]
  }
}

module DynamicPkv {
  import PKV = PackedKV
  import PSA = PackedStringArray
  import opened KeyType
  import opened ValueType`Internal
  import opened ValueMessage`Internal
  import opened NativeTypes
  import Seq = Sequences
  import Uint64_Order
  import LexOrder = Lexicographic_Byte_Order
  import opened BucketsLib
  import BucketModel
  import opened BucketWeights
  import opened Bounds
  import KeyspaceImpl = Lexicographic_Byte_Order_Impl
  
  datatype Capacity = Capacity(num_kv_pairs: uint32, total_key_len: uint32, total_message_len: uint32)

  function method EmptyCapacity() : Capacity
  {
    Capacity(0, 0, 0)
  }

  lemma PSAPushBackWeight(pkv: PKV.Pkv, key: Key, msg: Message)
  requires PKV.WF(pkv)
  ensures WeightKeyList(PSA.I(pkv.keys) + [key])
      == WeightKeyList(PSA.I(pkv.keys)) + WeightKey(key)
  ensures WeightMessageList(PKV.IMessages(pkv.messages) + [msg])
      == WeightMessageList(PKV.IMessages(pkv.messages)) + WeightMessage(msg)
  {
    WeightKeyListPushBack(PSA.I(pkv.keys), key);
    WeightMessageListPushBack(PKV.IMessages(pkv.messages), msg);
  }

  lemma PSAPopFrontWeight(pkv: PKV.Pkv, a: uint64, b: uint64)
  requires PKV.WF(pkv)
  requires 0 <= a < b <= PKV.NumKVPairs(pkv)
  ensures WeightKey(PKV.GetKey(pkv, a))
       + WeightKeyList(PSA.I(pkv.keys)[a+1..b])
      == WeightKeyList(PSA.I(pkv.keys)[a..b]);
  ensures WeightMessage(PKV.GetMessage(pkv, a))
       + WeightMessageList(PKV.IMessages(pkv.messages)[a+1..b])
      == WeightMessageList(PKV.IMessages(pkv.messages)[a..b]);
  {
    calc {
      WeightKey(PKV.GetKey(pkv, a)) + WeightKeyList(PSA.I(pkv.keys)[a+1..b]);
      WeightKey(PSA.I(pkv.keys)[a]) + WeightKeyList(PSA.I(pkv.keys)[a+1..b]);
      {
        WeightKeyListPushFront(PSA.I(pkv.keys)[a],
            PSA.I(pkv.keys)[a+1..b]);
        assert [PSA.I(pkv.keys)[a]] + PSA.I(pkv.keys)[a+1..b]
            == PSA.I(pkv.keys)[a..b];
      }
      WeightKeyList(PSA.I(pkv.keys)[a..b]);
    }
    calc {
      WeightMessage(PKV.GetMessage(pkv, a)) + WeightMessageList(PKV.IMessages(pkv.messages)[a+1..b]);
      {
        WeightMessageListPushFront(PKV.IMessages(pkv.messages)[a],
            PKV.IMessages(pkv.messages)[a+1..b]);
        assert [PKV.IMessages(pkv.messages)[a]] + PKV.IMessages(pkv.messages)[a+1..b]
            == PKV.IMessages(pkv.messages)[a..b];
      }
      WeightMessageList(PKV.IMessages(pkv.messages)[a..b]);
    }
  }

  lemma PSAPopFrontWeightSuffix(pkv: PKV.Pkv, a: uint64)
  requires PKV.WF(pkv)
  requires 0 <= a < PKV.NumKVPairs(pkv)
  ensures WeightKey(PKV.GetKey(pkv, a))
       + WeightKeyList(PSA.I(pkv.keys)[a+1..])
      == WeightKeyList(PSA.I(pkv.keys)[a..]);
  ensures WeightMessage(PKV.GetMessage(pkv, a))
       + WeightMessageList(PKV.IMessages(pkv.messages)[a+1..])
      == WeightMessageList(PKV.IMessages(pkv.messages)[a..]);
  {
    PSAPopFrontWeight(pkv, a, PKV.NumKVPairs(pkv));
    assert PSA.I(pkv.keys)[a+1..]
        == PSA.I(pkv.keys)[a+1..PKV.NumKVPairs(pkv)];
    assert PSA.I(pkv.keys)[a..]
        == PSA.I(pkv.keys)[a..PKV.NumKVPairs(pkv)];
    assert PKV.IMessages(pkv.messages)[a+1..]
        == PKV.IMessages(pkv.messages)[a+1..PKV.NumKVPairs(pkv)];
    assert PKV.IMessages(pkv.messages)[a..]
        == PKV.IMessages(pkv.messages)[a..PKV.NumKVPairs(pkv)];
  }

  function WeightBucketPkv(pkv: PKV.Pkv) : int
  requires PKV.WF(pkv)
  {
    WeightKeyList(PSA.I(pkv.keys))
      + WeightMessageList(PKV.IMessages(pkv.messages))
  }

  lemma WeightBucketPkv_eq_WeightPkv(pkv: PKV.Pkv)
  requires PKV.WF(pkv)
  decreases PKV.NumKVPairs(pkv)
  ensures PKV.WeightPkv(pkv) as int == WeightBucketPkv(pkv)
  {
    if |pkv.keys.offsets| == 0 {
      calc {
        PKV.WeightPkv(pkv) as int;
        0;
        WeightBucketPkv(pkv);
      }
    } else {
      var pkv' := PKV.subPkv(pkv, 0, PKV.NumKVPairs(pkv) - 1);
      var key := PKV.GetKey(pkv, PKV.NumKVPairs(pkv) -  1);
      var msg := PKV.GetMessage(pkv, PKV.NumKVPairs(pkv) - 1);
      var keys' := PKV.IKeys(pkv'.keys);
      var msgs' := PKV.IMessages(pkv'.messages);
      var keys := PKV.IKeys(pkv.keys);
      var msgs := PKV.IMessages(pkv.messages);
      calc {
        PKV.WeightPkv(pkv) as int;
        {
          //assert |pkv'.keys.offsets| == |pkv.keys.offsets| - 1;
          //assert |pkv'.messages.offsets| == |pkv.messages.offsets| - 1;
          //assert |pkv'.keys.data| == |pkv.keys.data| - |key|;
          assert |PSA.I(pkv.messages)[PKV.NumKVPairs(pkv) - 1]|
              <= ValueType.MaxLen() as int;
          /*assert PKV.Message_to_bytestring(msg)
              == PKV.Message_to_bytestring(PKV.bytestring_to_Message(
                    PSA.psaElement(pkv.messages, PKV.NumKVPairs(pkv) - 1)))
              == PSA.psaElement(pkv.messages, PKV.NumKVPairs(pkv) - 1);
          assert |pkv'.messages.data|
              == |pkv.messages.data| - |PSA.psaElement(pkv.messages, PKV.NumKVPairs(pkv) - 1)|
              == |pkv.messages.data| - |PKV.Message_to_bytestring(msg)|;*/
        }
        PKV.WeightPkv(pkv') as int + WeightKey(key) + WeightMessage(msg);
        { WeightBucketPkv_eq_WeightPkv(pkv'); }
        WeightBucketPkv(pkv') + WeightKey(key) + WeightMessage(msg);
        WeightKeyList(keys') + WeightMessageList(msgs') + WeightKey(key) + WeightMessage(msg);
        {
          IMessagesSlice(pkv, 0, PKV.NumKVPairs(pkv) -  1);
          assert keys' + [key] == keys;
          assert msgs' + [msg] == msgs;
          WeightKeyListPushBack(keys', key);
          WeightMessageListPushBack(msgs', msg);
        }
        WeightKeyList(keys) + WeightMessageList(msgs);
        WeightBucketPkv(pkv);
      }
    }
  }

  function PkvWeightBound() : int
  {
    10*(Uint32UpperBound() - 1)
  }

//~  lemma PkvWeightBounds(pkv: PKV.Pkv)
//~    requires PKV.WF(pkv)
//~    ensures PKV.WeightPkv(pkv) as nat <= PkvWeightBound()
//~  {
//~    WeightBucketPkv_eq_WeightPkv(pkv);
//~  }
  
  class DynamicPkv {
    var keys: PKV.PSA.DynamicPsa
    var messages: PKV.PSA.DynamicPsa
    ghost var Repr: set<object>

    predicate WF()
      reads this, this.Repr
    {
      && this in Repr
      && keys in Repr
      && keys.Repr <= Repr
      && messages in Repr
      && messages.Repr <= Repr
      && {this} !! keys.Repr !! messages.Repr 
      && keys.WF()
      && messages.WF()
      && PKV.WF(PKV.Pkv(keys.toPsa(), messages.toPsa()))
    }

    function method toPkv() : PKV.Pkv
      requires WF()
      reads this, this.Repr
    {
      PKV.Pkv(keys.toPsa(), messages.toPsa())
    }

    function method weight() : uint64
      requires WF()
      reads this, this.Repr
    {
      keys.weight() + messages.weight()
    }
    
    method AppendEncodedMessage(key: Key, msg: seq<byte>)
      requires WF()
      requires PKV.canAppend(toPkv(), key, msg)
      ensures WF()
      ensures toPkv() == PKV.AppendEncodedMessage(old(toPkv()), key, msg)
      ensures fresh(Repr - old(Repr))
      modifies this, Repr
    {
      keys.Append(key);
      messages.Append(msg);
      Repr := {this} + keys.Repr + messages.Repr;
      assert PKV.Pkv(keys.toPsa(), messages.toPsa()) == PKV.AppendEncodedMessage(old(toPkv()), key, msg);
    }
    
    method Append(key: Key, msg: Message)
      requires WF()
      requires msg.Define?
      requires PKV.NumKVPairs(toPkv()) < 0x1_0000_0000 - 1
      requires WeightKey(key) + WeightMessage(msg) + WeightKeyList(PKV.IKeys(toPkv().keys)) + WeightMessageList(PKV.IMessages(toPkv().messages)) < 0x1_0000_0000
      ensures WF()
      //ensures toPkv() == PKV.Append(old(toPkv()), key, msg)
      ensures PKV.IKeys(toPkv().keys) == PKV.IKeys(old(toPkv()).keys) + [key]
      ensures PKV.IMessages(toPkv().messages)
        == PKV.IMessages(old(toPkv()).messages) + [msg]
      ensures fresh(Repr - old(Repr))
      modifies this, Repr
    {
      WeightBucketPkv_eq_WeightPkv(toPkv());
      PSA.psaAppendIAppend(toPkv().keys, key);
      PSA.psaAppendIAppend(toPkv().messages, Message_to_bytestring(msg));

      AppendEncodedMessage(key, Message_to_bytestring(msg));

      calc {
        PKV.IMessages(toPkv().messages);
        {
          var a := PKV.IMessages(toPkv().messages);
          var b := PKV.IMessages(old(toPkv()).messages) + [msg];
          assert |a| == |b|;
          forall i | 0 <= i < |a|
          ensures a[i] == b[i]
          {
            if i == |a| - 1 {
              assert a[i] == b[i];
            } else {
              assert a[i] == b[i];
            }
          }
        }
        PKV.IMessages(old(toPkv()).messages) + [msg];
      }
    }

    method AppendPkv(pkv: PKV.Pkv, start: uint64, end: uint64)
    requires WF()
    requires PKV.WF(pkv)
    requires 0 <= start <= end <= PKV.NumKVPairs(pkv)
    requires PKV.NumKVPairs(toPkv()) + end - start <= 0x1_0000_0000 - 1
    requires WeightKeyList(PKV.IKeys(toPkv().keys)) + WeightKeyList(PSA.I(pkv.keys)[start..end])
          + WeightMessageList(PKV.IMessages(toPkv().messages)) + WeightMessageList(PKV.IMessages(pkv.messages)[start..end]) < 0x1_0000_0000
    ensures WF()
    ensures fresh(Repr - old(Repr))
    ensures PSA.I(toPkv().keys) == PSA.I(old(toPkv()).keys) + PSA.I(pkv.keys)[start..end]
    ensures PKV.IMessages(toPkv().messages) == PKV.IMessages(old(toPkv().messages)) + PKV.IMessages(pkv.messages)[start..end]
    ensures WeightKeyList(PKV.IKeys(toPkv().keys))
      == WeightKeyList(PKV.IKeys(old(toPkv()).keys)) + WeightKeyList(PSA.I(pkv.keys)[start..end])
    ensures WeightMessageList(PKV.IMessages(toPkv().messages))
      == WeightMessageList(PKV.IMessages(old(toPkv()).messages)) + WeightMessageList(PKV.IMessages(pkv.messages)[start..end])
    modifies this, Repr
    {
      var i := start;
      while i < end
      invariant start <= i <= end
      invariant WF()
      invariant PKV.NumKVPairs(old(toPkv())) + end - start <= 0x1_0000_0000 - 1
      invariant fresh(Repr - old(Repr))
      invariant PSA.I(toPkv().keys) == PSA.I(old(toPkv()).keys) + PSA.I(pkv.keys)[start..i]
      invariant PKV.IMessages(toPkv().messages) == PKV.IMessages(old(toPkv().messages)) + PKV.IMessages(pkv.messages)[start..i]
      invariant WeightKeyList(PKV.IKeys(toPkv().keys)) + WeightKeyList(PKV.IKeys(pkv.keys)[i..end])
            + WeightMessageList(PKV.IMessages(toPkv().messages)) + WeightMessageList(PKV.IMessages(pkv.messages)[i..end]) < 0x1_0000_0000
      invariant WeightKeyList(PKV.IKeys(toPkv().keys))
        == WeightKeyList(PKV.IKeys(old(toPkv()).keys)) + WeightKeyList(PSA.I(pkv.keys)[start..i])
      invariant WeightMessageList(PKV.IMessages(toPkv().messages))
        == WeightMessageList(PKV.IMessages(old(toPkv()).messages)) + WeightMessageList(PKV.IMessages(pkv.messages)[start..i])
      {
        var key := PKV.GetKey(pkv, i);
        var msg := PKV.GetMessage(pkv, i);

        PSAPopFrontWeight(pkv, i, end);
        PSAPushBackWeight(toPkv(), key, msg);
        
        Append(key, msg);

        calc {
          PSA.I(pkv.keys)[start..i+1];
          PSA.I(pkv.keys)[start..i] + [key];
        }
        calc {
          PKV.IMessages(pkv.messages)[start..i+1];
          PKV.IMessages(pkv.messages)[start..i] + [msg];
        }

        calc {
          WeightKeyList(PSA.I(pkv.keys)[start..i+1]);
          { WeightKeyListPushBack(PSA.I(pkv.keys)[start..i], key); }
          WeightKeyList(PSA.I(pkv.keys)[start..i]) + WeightKey(key);
        }
        calc {
          WeightMessageList(PKV.IMessages(pkv.messages)[start..i+1]);
          { WeightMessageListPushBack(PKV.IMessages(pkv.messages)[start..i], msg); }
          WeightMessageList(PKV.IMessages(pkv.messages)[start..i]) + WeightMessage(msg);
        }

        i := i + 1;
      }
    }

    predicate hasCapacity(cap: Capacity)
      requires WF()
      reads Repr
    {
      && cap.num_kv_pairs as int <= keys.offsets.Length
      && cap.total_key_len as int <= keys.data.Length
      && cap.num_kv_pairs as int <= messages.offsets.Length
      && cap.total_message_len as int <= messages.data.Length
    }

    constructor PreSized(capacity: Capacity)
      ensures WF()
      ensures hasCapacity(capacity)
      ensures toPkv() == PKV.EmptyPkv()
      ensures fresh(Repr)
    {
      keys := new PKV.PSA.DynamicPsa.PreSized(capacity.num_kv_pairs, capacity.total_key_len);
      messages := new PKV.PSA.DynamicPsa.PreSized(capacity.num_kv_pairs, capacity.total_message_len);
      new;
      Repr := {this} + keys.Repr + messages.Repr;
    }
  }

  lemma WeightEmptySeq()
  ensures WeightKeyList([]) == 0
  ensures WeightMessageList([]) == 0
  {
  }
  
  datatype SingleMergeResult =
      MergeCompleted(bot: PKV.Pkv, slack: uint64)
    | SlackExhausted(bot: PKV.Pkv, end: uint64, slack: uint64)
  {
    predicate WF()
    {
      && PKV.WF(this.bot)
    }

    function I() : BucketModel.singleMergeResult
    requires WF()
    {
      match this {
        case MergeCompleted(bot, slack) =>
          BucketModel.MergeCompleted(
            PSA.I(bot.keys),
            PKV.IMessages(bot.messages),
            slack as nat)
        case SlackExhausted(bot, end, slack) =>
          BucketModel.SlackExhausted(
            PSA.I(bot.keys),
            PKV.IMessages(bot.messages),
            end as nat,
            slack as nat)
      }
    }
  }

  method MergeToOneChild(top: PKV.Pkv, from0: uint64, to: uint64, bot: PKV.Pkv, slack0: uint64)
    returns (result: SingleMergeResult)
    requires PKV.WF(top)
    requires PKV.WF(bot)
    requires from0 <= to <= PKV.NumKVPairs(top)
    requires 0 <= PKV.NumKVPairs(top) < 0x1000_0000
    requires 0 <= PKV.NumKVPairs(bot) < 0x1000_0000
    requires WeightBucketPkv(bot) as int + slack0 as int
        <= MaxTotalBucketWeight()
    ensures result.WF()
    ensures result.I() == BucketModel.mergeToOneChild(
        PSA.I(top.keys), PKV.IMessages(top.messages),
        from0 as nat, to as nat,
        PSA.I(bot.keys), PKV.IMessages(bot.messages),
        0, [], [],
        slack0 as nat)
    ensures WeightKeyList(PKV.IKeys(result.bot.keys)) +
          WeightMessageList(PKV.IMessages(result.bot.messages)) +
          result.slack as int
       == WeightKeyList(PKV.IKeys(bot.keys)) +
          WeightMessageList(PKV.IMessages(bot.messages)) +
          slack0 as int
  {
    BucketModel.reveal_mergeToOneChild();

    var from: uint64 := from0;
    var slack: uint64 := slack0;
    var bot_from: uint64 := 0;

    assert PSA.psaTotalLength(bot.keys) as int <= MaxTotalBucketWeight() by {
      WeightBucketPkv_eq_WeightPkv(bot);
    }
    assert PSA.psaTotalLength(bot.messages) as int <= MaxTotalBucketWeight() by {
      WeightBucketPkv_eq_WeightPkv(bot);
    }

    var maxkeys: uint32 := (to - from + PKV.NumKVPairs(bot)) as uint32;
    var maxkeyspace: uint32 := (PSA.psaTotalLength(bot.keys) + slack) as uint32;
    var maxmsgspace: uint32 := (PSA.psaTotalLength(bot.messages) + slack) as uint32;
    var cap := Capacity(maxkeys, maxkeyspace, maxmsgspace);
    var dresult := new DynamicPkv.PreSized(cap);

    //assert PKV.subPkv(bot, bot_from, PKV.NumKVPairs(bot))
    //    == bot;

    WeightEmptySeq();
    assert WeightBucketPkv(dresult.toPkv()) == 0;

    while true
    invariant from <= to
    invariant bot_from <= PKV.NumKVPairs(bot)
    invariant dresult.WF()
    invariant fresh(dresult.Repr)
    invariant BucketModel.mergeToOneChild(
          PSA.I(top.keys), PKV.IMessages(top.messages),
          from0 as nat, to as nat,
          PSA.I(bot.keys), PKV.IMessages(bot.messages),
          0, [], [],
          slack0 as nat)
     == BucketModel.mergeToOneChild(
          PSA.I(top.keys), PKV.IMessages(top.messages),
          from as nat, to as nat,
          PSA.I(bot.keys), PKV.IMessages(bot.messages),
          bot_from as nat,
          PSA.I(dresult.toPkv().keys),
          PKV.IMessages(dresult.toPkv().messages),
          slack as nat)
    invariant PKV.NumKVPairs(dresult.toPkv()) as int
        <= bot_from as int + from as int - from0 as int
    invariant WeightBucketPkv(bot) + slack0 as int
        == WeightBucketPkv(dresult.toPkv())
          //+ WeightBucketPkv(PKV.subPkv(bot, bot_from, PKV.NumKVPairs(bot)))
          + WeightKeyList(PKV.IKeys(bot.keys)[bot_from..])
          + WeightMessageList(PKV.IMessages(bot.messages)[bot_from..])
          + slack as int
    decreases PKV.NumKVPairs(top) as int + PKV.NumKVPairs(bot) as int
          - from as int - bot_from as int
    {
      //WeightBucketPkv_eq_WeightPkv(dresult.toPkv());

      if from == to {
        assert PKV.IKeys(bot.keys)[bot_from..]
            == PKV.IKeys(bot.keys)[bot_from..PKV.NumKVPairs(bot)];
        assert PKV.IMessages(bot.messages)[bot_from..]
            == PKV.IMessages(bot.messages)[bot_from..PKV.NumKVPairs(bot)];

        dresult.AppendPkv(bot, bot_from, PKV.NumKVPairs(bot));
        result := MergeCompleted(dresult.toPkv(), slack);
        return;
      } else {
        var topkey := PSA.psaElement(top.keys, from);
        var botkey;
        var c;
        if bot_from < PKV.NumKVPairs(bot) {
          botkey := PSA.psaElement(bot.keys, bot_from);
          c := KeyspaceImpl.cmp(topkey, botkey);
        }

        if bot_from < PKV.NumKVPairs(bot) && c == 0 {
          var key := topkey;
          var topmsg := PKV.GetMessage(top, from);
          var botmsg := PKV.GetMessage(bot, bot_from);
          var msg := ValueMessage.Merge(topmsg, botmsg);
          if msg == IdentityMessage() {
            from := from + 1;
            bot_from := bot_from + 1;
            slack := slack
                + WeightKeyUint64(key)
                + WeightMessageUint64(botmsg);
          } else {
            var wm1 := WeightMessageUint64(msg);
            var wm2 := WeightMessageUint64(botmsg);
            if wm1 > slack + wm2 {
              assert PKV.IKeys(bot.keys)[bot_from..]
                  == PKV.IKeys(bot.keys)[bot_from..PKV.NumKVPairs(bot)];
              assert PKV.IMessages(bot.messages)[bot_from..]
                  == PKV.IMessages(bot.messages)[bot_from..PKV.NumKVPairs(bot)];

              dresult.AppendPkv(bot, bot_from, PKV.NumKVPairs(bot));
              result := SlackExhausted(dresult.toPkv(), from, slack);
              return;
            } else {
              PSAPopFrontWeight(top, from, to);
              PSAPopFrontWeightSuffix(bot, bot_from);
              PSAPushBackWeight(dresult.toPkv(), key, msg);

              dresult.Append(key, msg);
              from := from + 1;
              bot_from := bot_from + 1;
              slack := slack + wm2 - wm1;
            }
          }
        } else if bot_from == PKV.NumKVPairs(bot) || c < 0 {
          var key := topkey;
          var msg := PKV.GetMessage(top, from);
          var delta := WeightKeyUint64(key) + WeightMessageUint64(msg);
          if delta > slack {
            assert PKV.IKeys(bot.keys)[bot_from..]
                == PKV.IKeys(bot.keys)[bot_from..PKV.NumKVPairs(bot)];
            assert PKV.IMessages(bot.messages)[bot_from..]
                == PKV.IMessages(bot.messages)[bot_from..PKV.NumKVPairs(bot)];

            dresult.AppendPkv(bot, bot_from, PKV.NumKVPairs(bot));
            result := SlackExhausted(dresult.toPkv(), from, slack);
            return;
          } else {
            PSAPopFrontWeight(top, from, to);
            PSAPushBackWeight(dresult.toPkv(), key, msg);

            dresult.Append(key, msg);
            from := from + 1;
            slack := slack - delta;
          }
        } else {
          var key := botkey;
          var msg := PKV.GetMessage(bot, bot_from);

          PSAPushBackWeight(dresult.toPkv(), key, msg);
          PSAPopFrontWeightSuffix(bot, bot_from);

          dresult.Append(key, msg);
          bot_from := bot_from + 1;
        }
      }
    }
  }

  function PKVISeq(s: seq<PKV.Pkv>) : (res: seq<Bucket>)
  requires forall i | 0 <= i < |s| :: PKV.WF(s[i])
  ensures |res| == |s|
  ensures forall i | 0 <= i < |s| :: PKV.I(s[i]) == res[i]
  {
    if |s| == 0 then [] else PKVISeq(Seq.DropLast(s)) + [PKV.I(Seq.Last(s))]
  }

  function seqInt(s: seq<uint64>) : (res: seq<int>)
  ensures |res| == |s|
  ensures forall i | 0 <= i < |s| :: res[i] == s[i] as int
  {
    if |s| == 0 then [] else seqInt(Seq.DropLast(s)) + [Seq.Last(s) as int]
  }

  datatype MergeResult = MergeResult(top: PKV.Pkv, bots: seq<PKV.Pkv>, slack: uint64)
  {
    predicate WF()
    {
      && PKV.WF(this.top)
      && forall i | 0 <= i < |this.bots| :: PKV.WF(this.bots[i])
    }

    function I() : BucketModel.mergeResult
    requires WF()
    {
      BucketModel.mergeResult(
        PKV.I(this.top),
        PKVISeq(this.bots),
        this.slack as nat
      )
    }
  }

  lemma WeightIthBucketLe(bots: seq<PKV.Pkv>, i: uint64)
  requires forall i | 0 <= i < |bots| :: PKV.WF(bots[i])
  requires 0 <= i as int < |bots|
  ensures WeightBucketPkv(bots[i]) 
      <= WeightBucketList(PKVISeq(bots[i..]))
  {
    WeightBucketLeBucketList(PKVISeq(bots[i..]), 0);
  }

  lemma IMessagesSlice(pkv: PKV.Pkv, a: uint64, b: uint64)
  requires PKV.WF(pkv)
  requires 0 <= a <= b <= PKV.NumKVPairs(pkv)
  ensures PKV.IMessages(pkv.messages)[a..b]
      == PKV.IMessages(PKV.subPkv(pkv, a, b).messages)
  {
    var x := PKV.IMessages(pkv.messages)[a..b];
    var y := PKV.IMessages(PKV.subPkv(pkv, a, b).messages);
    assert |x| == |y|;
    forall i | 0 <= i < |x|
    ensures x[i] == y[i];
    {
      calc {
        x[i];
        PKV.IMessages(pkv.messages)[a as int + i];
        bytestring_to_Message(PSA.I(pkv.messages)[a as int + i]);
        y[i];
      }
    }
  }

  lemma WeightPKVListPopFront(pkvs: seq<PKV.Pkv>, i: int)
  requires forall j | 0 <= j < |pkvs| :: PKV.WF(pkvs[j])
  requires 0 <= i < |pkvs|
  ensures forall j | 0 <= j < |pkvs[i..]| :: PKV.WF(pkvs[i..][j])
  ensures forall j | 0 <= j < |pkvs[i+1..]| :: PKV.WF(pkvs[i+1..][j])
  ensures WeightBucketList(PKVISeq(pkvs[i..]))
      == WeightBucketList(PKVISeq(pkvs[i+1..]))
          + WeightKeyList(PKV.IKeys(pkvs[i].keys))
          + WeightMessageList(PKV.IMessages(pkvs[i].messages))
  {
    WeightBucketListConcat([PKV.I(pkvs[i])], PKVISeq(pkvs[i+1..]));
    assert [PKV.I(pkvs[i])] + PKVISeq(pkvs[i+1..])
        == PKVISeq(pkvs[i..]);
    assert WeightBucketList([PKV.I(pkvs[i])]) == WeightBucket(PKV.I(pkvs[i])) by {
      reveal_WeightBucketList();
    }
  }

  lemma WeightPKVArrayPushBack(pkvs: array<PKV.Pkv>, i: int)
  requires 0 <= i < pkvs.Length
  requires forall j | 0 <= j < i+1 :: PKV.WF(pkvs[j])
  ensures forall j | 0 <= j < |pkvs[..i]| :: PKV.WF(pkvs[..i][j])
  ensures forall j | 0 <= j < |pkvs[..i+1]| :: PKV.WF(pkvs[..i+1][j])
  ensures WeightBucketList(PKVISeq(pkvs[..i]))
          + WeightKeyList(PKV.IKeys(pkvs[i].keys))
          + WeightMessageList(PKV.IMessages(pkvs[i].messages))
      == WeightBucketList(PKVISeq(pkvs[..i+1]))
  {
    WeightBucketListConcat(PKVISeq(pkvs[..i]), [PKV.I(pkvs[i])]);
    assert PKVISeq(pkvs[..i]) + [PKV.I(pkvs[i])]
        == PKVISeq(pkvs[..i+1]);
    assert WeightBucketList([PKV.I(pkvs[i])]) == WeightBucket(PKV.I(pkvs[i])) by {
      reveal_WeightBucketList();
    }
  }

  method MergeToChildrenIter(
    top: PKV.Pkv, 
    bots: seq<PKV.Pkv>,
    idxs: seq<uint64>,
    tmp: SingleMergeResult,
    i: uint64,
    results: array<PKV.Pkv>)
  returns (res: MergeResult)
  requires PKV.WF(top)
  requires forall i | 0 <= i < |bots| :: PKV.WF(bots[i])
  requires |bots| < 0x1_0000_0000_0000_0000
  requires 0 <= |PKV.IKeys(top.keys)| < 0x1000_0000
  requires forall i | 0 <= i < |bots| :: |PKV.IKeys(bots[i].keys)| < 0x1000_0000
  requires 0 < |bots|
  requires results.Length == |bots|
  requires 0 <= i as int <= |bots|
  requires |idxs| == |bots| - 1
  requires forall i | 0 <= i < |idxs| :: 0 <= idxs[i] as int <= |PKV.IKeys(top.keys)|
  requires tmp.SlackExhausted? ==> 0 <= tmp.end as int <= |PKV.IKeys(top.keys)|
  requires tmp.WF()
  requires forall j | 0 <= j < i :: PKV.WF(results[j])
  requires WeightBucketList(PKVISeq(results[..i]))
      + WeightBucketList(PKVISeq(bots[i..]))
      + tmp.slack as int == MaxTotalBucketWeight()
  decreases |bots| - i as int
  modifies results
  ensures res.WF()
  ensures res.I() == BucketModel.mergeToChildrenIter(
      PKV.I(top), PKVISeq(bots), seqInt(idxs), tmp.I(), i as int, 
          PKVISeq(old(results[..i])))
  {
    if i == |bots| as uint64 {
      if tmp.SlackExhausted? {
        var leftover_top := PKV.SubPkv(top, tmp.end, PKV.NumKVPairs(top));

        ghost var topb := PKV.I(top);
        calc
        {
          BucketOfSeq(topb.keys[tmp.end..], topb.msgs[tmp.end..]);
          {
            assert PKV.IKeys(top.keys)[tmp.end..]
                == PKV.IKeys(top.keys)[tmp.end..PKV.NumKVPairs(top)];
            assert PKV.IMessages(top.messages)[tmp.end..]
                == PKV.IMessages(top.messages)[tmp.end..PKV.NumKVPairs(top)];
            assert PKV.I(leftover_top).keys == topb.keys[tmp.end..];
            IMessagesSlice(top, tmp.end, PKV.NumKVPairs(top));
            assert PKV.I(leftover_top).msgs == topb.msgs[tmp.end..];
          }
          PKV.I(leftover_top);
        }

        assert results[..] == results[..i];

        return MergeResult(leftover_top, results[..], tmp.slack);
      } else {
        return MergeResult(PKV.EmptyPkv(), results[..], tmp.slack);
      }
    } else {
      if tmp.MergeCompleted? {
        var from := if i == 0 then 0 else idxs[i-1];
        var to1 := if i == |idxs| as uint64 then PKV.NumKVPairs(top) else idxs[i];
        var to := if to1 < from then from else to1;

        WeightIthBucketLe(bots, i);

        var tmp' := MergeToOneChild(top, from, to, bots[i], tmp.slack);
        results[i] := tmp'.bot;

        calc {
          WeightBucketList(PKVISeq(results[..i]))
            + WeightBucketList(PKVISeq(bots[i..]))
            + tmp.slack as int;
          {
            WeightPKVListPopFront(bots, i as int);
            WeightPKVArrayPushBack(results, i as int);
          }
          WeightBucketList(PKVISeq(results[..i+1]))
            + WeightBucketList(PKVISeq(bots[i+1..]))
            + tmp'.slack as int;
        }

        calc {
          PKVISeq(results[..i+1]);
          PKVISeq(old(results[..i])) + [BucketOfSeq(PKV.IKeys(tmp'.bot.keys), PKV.IMessages(tmp'.bot.messages))];
        }

        res := MergeToChildrenIter(top, bots, idxs, tmp', i+1, results);
        return;
      } else {
        results[i] := bots[i];

        calc {
          WeightBucketList(PKVISeq(results[..i]))
            + WeightBucketList(PKVISeq(bots[i..]));
          {
            WeightPKVListPopFront(bots, i as int);
            WeightPKVArrayPushBack(results, i as int);
          }
          WeightBucketList(PKVISeq(results[..i+1]))
            + WeightBucketList(PKVISeq(bots[i+1..]));
        }

        calc {
          PKVISeq(results[..i+1]);
          PKVISeq(old(results[..i])) + [PKV.I(bots[i])];
        }

        res := MergeToChildrenIter(top, bots, idxs, tmp, i+1, results);
        return;
      }
    }
  }

  method computePivotIndexes(keys: PSA.Psa, pivots: seq<Key>)
  returns (pivotIdxs: seq<uint64>)
    requires PSA.WF(keys)
    requires |PSA.I(keys)| < Uint64UpperBound()
    requires |pivots| < Uint64UpperBound() - 1
    ensures |pivotIdxs| == |pivots|
    ensures forall i | 0 <= i < |pivots| :: pivotIdxs[i] as nat
        == LexOrder.binarySearchIndexOfFirstKeyGte(PSA.I(keys), pivots[i])
  {
    var results := new uint64[|pivots| as uint64];
    var i : uint64 := 0;
    while i < |pivots| as uint64
      invariant i <= |pivots| as uint64
      invariant forall j | 0 <= j < i :: results[j] as nat
          == LexOrder.binarySearchIndexOfFirstKeyGte(PSA.I(keys), pivots[j])
    {
      results[i] := PSA.BinarySearchIndexOfFirstKeyGte(keys, pivots[i]);
      i := i + 1;
    }

    pivotIdxs := results[..];
  }
 
  method MergeToChildren(
      top: PKV.Pkv,
      pivots: seq<Key>,
      bots: seq<PKV.Pkv>,
      slack: uint64)
  returns (result: MergeResult)
  requires PKV.WF(top)
  requires forall i | 0 <= i < |bots| :: PKV.WF(bots[i])
  requires 0 <= |PKV.IKeys(top.keys)| < 0x1000_0000
  requires forall i | 0 <= i < |bots| :: |PKV.IKeys(bots[i].keys)| < 0x1000_0000
  requires 0 < |bots| == |pivots| + 1 < Uint64UpperBound()
  requires WeightBucketList(PKVISeq(bots)) + slack as int == MaxTotalBucketWeight()

  ensures result.WF()
  ensures result.I() == BucketModel.mergeToChildren(
      PKV.I(top), pivots, PKVISeq(bots), slack as int)
  {
    BucketModel.reveal_mergeToChildren();

    var idxs := computePivotIndexes(top.keys, pivots);
    var tmp := MergeCompleted(PKV.EmptyPkv(), slack);
    var ar := new PKV.Pkv[|bots| as uint64];

    assert WeightBucketList(PKVISeq(ar[..0])) == 0 by { reveal_WeightBucketList(); }
    assert bots[0..] == bots;
    assert BucketModel.pivotIndexes(PKV.I(top).keys, pivots) == seqInt(idxs);

    result := MergeToChildrenIter(top, bots, idxs, tmp, 0, ar);
  }

  datatype PartialFlushResult = PartialFlushResult(top: PKV.Pkv, bots: seq<PKV.Pkv>)
  {
    predicate WF()
    {
      && PKV.WF(top)
      && forall i | 0 <= i < |bots| :: PKV.WF(bots[i])
    }

    function I() : BucketModel.partialFlushResult
    requires WF()
    {
      BucketModel.partialFlushResult(PKV.I(top), PKVISeq(bots))
    }
  }

  method PartialFlush(
      top: PKV.Pkv,
      pivots: seq<Key>,
      bots: seq<PKV.Pkv>)
  returns (result: PartialFlushResult)
  requires PKV.WF(top)
  requires forall i | 0 <= i < |bots| :: PKV.WF(bots[i])
  requires 0 <= |PKV.IKeys(top.keys)| < 0x1000_0000
  requires forall i | 0 <= i < |bots| :: |PKV.IKeys(bots[i].keys)| < 0x1000_0000
  requires 0 < |bots| == |pivots| + 1 < Uint64UpperBound()
  requires WeightBucketList(PKVISeq(bots)) <= MaxTotalBucketWeight()
  ensures result.WF()
  ensures result.I() == BucketModel.partialFlush(
      PKV.I(top), pivots, PKVISeq(bots))
  {
    var slack := MaxTotalBucketWeightUint64();
    var i := 0;

    assert WeightBucketList(PKVISeq(bots)[..i]) == 0 by { reveal_WeightBucketList(); }

    while i < |bots| as uint64
    invariant 0 <= i as int <= |bots|
    invariant slack as int == MaxTotalBucketWeight() - WeightBucketList(PKVISeq(bots)[..i])
    {
      calc {
        WeightBucketList(PKVISeq(bots)[..i+1]);
        {
          assert Seq.DropLast(PKVISeq(bots)[..i+1]) == PKVISeq(bots)[..i];
          assert Seq.Last(PKVISeq(bots)[..i+1]) == PKVISeq(bots)[i];
          reveal_WeightBucketList();
        }
        WeightBucketList(PKVISeq(bots)[..i]) + WeightBucket(PKVISeq(bots)[i]);
        {
          WeightBucketPkv_eq_WeightPkv(bots[i]);
          //WeightBucket_eq_WeightSeqs(PKV.I(bots[i]));
          assert WeightBucket(PKVISeq(bots)[i])
              == WeightBucket(PKV.I(bots[i]))
              == PKV.WeightPkv(bots[i]) as int;
        }
        WeightBucketList(PKVISeq(bots)[..i]) + PKV.WeightPkv(bots[i]) as int;
      }
      WeightBucketListSlice(PKVISeq(bots), 0, (i+1) as int);

      slack := slack - PKV.WeightPkv(bots[i]);
      i := i + 1;
    }
    assert PKVISeq(bots)[..i] == PKVISeq(bots);

    BucketModel.reveal_partialFlush();
    var res := MergeToChildren(top, pivots, bots, slack);
    return PartialFlushResult(res.top, res.bots);
  }
}
