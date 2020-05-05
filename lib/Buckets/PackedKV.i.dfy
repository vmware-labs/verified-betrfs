include "PackedStringArray.i.dfy"
include "BucketsLib.i.dfy"

module PackedKV {
  import PSA = PackedStringArray
  import opened NativeTypes
  import KeyspaceImpl = Lexicographic_Byte_Order_Impl
  import Keyspace = KeyspaceImpl.Ord
  import opened KeyType
  import opened ValueType`Internal
  import opened ValueMessage
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

  predicate ValidMessageByteString(s: seq<byte>)
  {
    |s| <= ValueType.MaxLen() as int
  }

  predicate ValidStringLens<A>(strs: seq<seq<A>>, upper_bound: nat)
  {
    forall i | 0 <= i < |strs| :: |strs[i]| <= upper_bound
  }

  predicate ValidKeyLens<A>(strs: seq<seq<A>>)
  {
    ValidStringLens(strs, KeyType.MaxLen() as nat)
  }

  predicate ValidMessageLens<A>(strs: seq<seq<A>>)
  {
    ValidStringLens(strs, ValueType.MaxLen() as nat)
  }

  function method bytestring_to_Message(s: seq<byte>) : Message
  requires |s| < 0x1_0000_0000
  {
    if |s| as uint64 <= ValueType.MaxLen() then (
      Define(s)
    ) else (
      // NOTE(travis)
      // It's just convenient to make this function total, so
      // we just do this if the byte string is invalid.
      Define(ValueType.DefaultValue())
    )
  }

  function method Message_to_bytestring(msg: Message) : seq<byte>
    requires msg.Define?
  {
    msg.value
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

  predicate WF(pkv: Pkv) {
    && PSA.WF(pkv.keys)
    && PSA.WF(pkv.messages)
    && |pkv.keys.offsets| == |pkv.messages.offsets|
    && ValidKeyLens(PSA.I(pkv.keys))
    && ValidMessageLens(PSA.I(pkv.messages))
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
    && ValidMessageByteString(msg)
  }

  function AppendEncodedMessage(pkv: Pkv, key: Key, msg: seq<byte>) : (result: Pkv)
    requires WF(pkv)
    requires canAppend(pkv, key, msg)
    ensures WF(result)
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

  lemma IMapAppend(pkv: Pkv, key: Key, msg: seq<byte>)
    requires WF(pkv)
    requires canAppend(pkv, key, msg)
    ensures IMap(AppendEncodedMessage(pkv, key, msg)) == IMap(pkv)[key := bytestring_to_Message(msg)]
  {
    PSA.psaAppendIAppend(pkv.keys, key);
    PSA.psaAppendIAppend(pkv.messages, msg);
    var keys := PSA.I(pkv.keys);
    var messages := IMessages(pkv.messages);
    var newpkv := AppendEncodedMessage(pkv, key, msg);
    var newkeys := PSA.I(newpkv.keys);
    var newmessages := IMessages(newpkv.messages);

    assert forall i | 0 <= i < |messages| :: Sequences.DropLast(newmessages)[i] == bytestring_to_Message(PSA.I(newpkv.messages)[i]);
    assert Sequences.DropLast(newmessages) == messages;
    assert Last(newmessages) == bytestring_to_Message(msg);

    calc {
      IMap(newpkv);
      { reveal_BucketMapOfSeq(); }
      BucketMapOfSeq(keys, messages)[key := bytestring_to_Message(msg)];
      { reveal_BucketMapOfSeq(); }
      IMap(pkv)[key := bytestring_to_Message(msg)];
    }
  }

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

  // TODO: add support for partial merges.  (slack is unused at the moment)
  function mergeToOneChild(top: Pkv, from: nat, to: nat, bot: Pkv, slack: uint64) : (result: Option<Pkv>)
    requires WF(top)
    requires WF(bot)
    requires from <= to <= NumKVPairs(top) as nat
    ensures result.Some? ==> WF(result.value)
    decreases to - from + NumKVPairs(bot) as nat
  {
    //assert 0 < NumKVPairs(top) ==> PSA.LastElement(top.keys) == Last(PSA.I(top.keys));
    //assert 0 < NumKVPairs(bot) ==> PSA.LastElement(bot.keys) == Last(PSA.I(bot.keys));
    if from == to then
      Some(bot)
    else if NumKVPairs(bot) == 0 then
      Some(subPkv(top, from as uint64, to as uint64))
    else if PSA.psaElement(top.keys, to as uint64 - 1) == PSA.LastElement(bot.keys) then (
      var submerge := mergeToOneChild(DropLast(top), from, to-1, DropLast(bot), slack);
      var key := PSA.psaElement(top.keys, to as uint64 - 1);
      assert key == PSA.I(top.keys)[to-1];
      var topmsg := bytestring_to_Message(PSA.psaElement(top.messages, to as uint64 - 1));
      var botmsg := bytestring_to_Message(PSA.LastElement(bot.messages));
      var msg := ValueMessage.Merge(topmsg, botmsg);
      var bytemsg := Message_to_bytestring(msg);
      if submerge == None || msg == IdentityMessage() then
        submerge
      else if !canAppend(submerge.value, key, bytemsg) then
        None
      else 
        Some(AppendEncodedMessage(submerge.value, key, bytemsg))
    ) else if Keyspace.lt(PSA.I(top.keys)[to - 1], Last(PSA.I(bot.keys))) then (
      var submerge := mergeToOneChild(top, from, to, DropLast(bot), slack);
      var key := PSA.LastElement(bot.keys);
      assert key == PSA.I(bot.keys)[PSA.psaNumStrings(bot.keys)-1];
      var msg := PSA.LastElement(bot.messages);
      if submerge == None || !canAppend(submerge.value, key, msg) then
        None
      else 
        Some(AppendEncodedMessage(submerge.value, key, msg))
    ) else (
      var submerge := mergeToOneChild(top, from, to-1, bot, slack);
      var key := PSA.psaElement(top.keys, to as uint64 - 1);
      assert key == PSA.I(top.keys)[to-1];
      var msg := PSA.LastElement(top.messages);
      if submerge == None || !canAppend(submerge.value, key, msg) then
        None
      else 
        Some(AppendEncodedMessage(submerge.value, key, msg))
    )    
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
  
  // lemma MergeWillSucceed(top: Pkv, bot: Pkv) returns (result: Pkv)
  //   requires WF(top)
  //   requires WF(bot)
  //   requires NumKVPairs(top) + NumKVPairs(bot) < 0x1_0000_0000
  //   requires PSA.psaTotalLength(top.keys) + PSA.psaTotalLength(bot.keys) < 0x1_0000_0000
  //   requires (NumKVPairs(top) as nat + NumKVPairs(bot) as nat) * (1 + ValueType.MaxLen() as nat) < 0x1_0000_0000
  //   ensures Merge(top, bot) == Some(result)
  //   ensures NumKVPairs(result) <= NumKVPairs(top) + NumKVPairs(bot)
  //   ensures PSA.psaTotalLength(result.keys) <= PSA.psaTotalLength(top.keys) + PSA.psaTotalLength(bot.keys)
  //   ensures PSA.psaTotalLength(result.messages) as nat
  //   <= (NumKVPairs(top) as nat + NumKVPairs(bot) as nat) * (1 + ValueType.MaxLen() as nat)
  //   decreases NumKVPairs(top) + NumKVPairs(bot)
  // {
  //   assert 0 < NumKVPairs(top) ==> PSA.LastElement(top.keys) == Last(PSA.I(top.keys));
  //   assert 0 < NumKVPairs(bot) ==> PSA.LastElement(bot.keys) == Last(PSA.I(bot.keys));
  //   if NumKVPairs(top) == 0 {
  //     psaTotalLengthBound(bot.messages, ValueType.MaxLen() as nat);
  //     result := bot;
  //   } else if NumKVPairs(bot) == 0 {
  //     psaTotalLengthBound(top.messages, ValueType.MaxLen() as nat);
  //     result := top;
  //   } else if PSA.LastElement(top.keys) == PSA.LastElement(bot.keys) {
  //     var submerge := Merge(DropLast(top), DropLast(bot));
  //     var key := PSA.LastElement(top.keys);
  //     var topmsg := bytestring_to_Message(PSA.LastElement(top.messages));
  //     var botmsg := bytestring_to_Message(PSA.LastElement(bot.messages));
  //     var msg := ValueMessage.Merge(topmsg, botmsg);
  //     var bytemsg := Message_to_bytestring(msg);
  //     var submergepsa := MergeWillSucceed(DropLast(top), DropLast(bot));
  //     if msg == IdentityMessage() {
  //       result := submergepsa;
  //     } else {
  //       result := AppendEncodedMessage(submerge.value, key, bytemsg);
  //     }
  //   } else if Keyspace.lt(PSA.LastElement(top.keys), PSA.LastElement(bot.keys)) {
  //     var submerge := Merge(top, DropLast(bot));
  //     var key := PSA.LastElement(bot.keys);
  //     var msg := PSA.LastElement(bot.messages);
  //     assert msg == Last(PSA.I(bot.messages));
  //     var submergepsa := MergeWillSucceed(top, DropLast(bot));
  //     result := AppendEncodedMessage(submerge.value, key, msg);
  //   } else {
  //     var submerge := Merge(DropLast(top), bot);
  //     var key := PSA.LastElement(top.keys);
  //     var msg := PSA.LastElement(top.messages);
  //     assert msg == Last(PSA.I(top.messages));
  //     var submergepsa := MergeWillSucceed(DropLast(top), bot);
  //     result := AppendEncodedMessage(submerge.value, key, msg);
  //   }
  // }

  // lemma MergeWillSucceedNoReturn(top: Pkv, bot: Pkv)
  //   requires WF(top)
  //   requires WF(bot)
  //   requires NumKVPairs(top) + NumKVPairs(bot) < 0x1_0000_0000
  //   requires PSA.psaTotalLength(top.keys) + PSA.psaTotalLength(bot.keys) < 0x1_0000_0000
  //   requires (NumKVPairs(top) as nat + NumKVPairs(bot) as nat) * (1 + ValueType.MaxLen() as nat) < 0x1_0000_0000
  //   ensures Merge(top, bot).Some?
  //   ensures NumKVPairs(Merge(top, bot).value) <= NumKVPairs(top) + NumKVPairs(bot)
  //   ensures PSA.psaTotalLength(Merge(top, bot).value.keys)
  //   <= PSA.psaTotalLength(top.keys) + PSA.psaTotalLength(bot.keys)
  //   ensures PSA.psaTotalLength(Merge(top, bot).value.messages) as nat
  //   <= (NumKVPairs(top) as nat + NumKVPairs(bot) as nat) * (1 + ValueType.MaxLen() as nat)
  // {
  //   var dummy := MergeWillSucceed(top, bot);
  // }

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
  
  // function mergeToChildren(top: Pkv, pivots: seq<Key>, bots: seq<Pkv>, slack: nat) : (result: seq<Option<Pkv>>)
  //   requires WF(top)
  //   requires Integer_Order.IsSorted(pivotIdxs)
  //   requires 0 < |bots| == |pivotIdxs|
  //   requires Last(pivotIdxs) <= NumKVPairs(top) as nat
  //   requires forall i | 0 <= i < |bots| :: WF(bots[i])
  // {
  //   // if |pivotIdxs| == 1 then
  //   //   [ mergeToOneChild(top, 0, pivotIdxs[0], bots[0]) ]
  //   // else
  //   //   Integer_Order.SortedSubsequence(pivotIdxs, 0, |pivotIdxs| - 1);
  //   //   Integer_Order.IsSortedImpliesLte(pivotIdxs, |pivotIdxs| - 2, |pivotIdxs| - 1);
  //   //   var submerge := mergeToChildren(top, Sequences.DropLast(pivotIdxs), Sequences.DropLast(bots));
  //   //   var lastmerge := mergeToOneChild(top, pivotIdxs[|pivotIdxs|-2], Last(pivotIdxs), Last(bots));
  //   //   submerge + [ lastmerge ]
  // }

}

module DynamicPkv {
  import PKV = PackedKV
  import PSA = PackedStringArray
  import opened KeyType
  import opened ValueType`Internal
  import opened ValueMessage
  import opened NativeTypes
  import Seq = Sequences
  import Uint64_Order
  import LexOrder = Lexicographic_Byte_Order
  import opened BucketsLib
  
  datatype Capacity = Capacity(num_kv_pairs: uint32, total_key_len: uint32, total_message_len: uint32)

  function method EmptyCapacity() : Capacity
  {
    Capacity(0, 0, 0)
  }
    
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
      requires PKV.canAppend(toPkv(), key, PKV.Message_to_bytestring(msg))
      ensures WF()
      ensures toPkv() == PKV.Append(old(toPkv()), key, msg)
      ensures fresh(Repr - old(Repr))
      modifies this, Repr
    {
      AppendEncodedMessage(key, PKV.Message_to_bytestring(msg));
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
  
  datatype SingleMergeResult =
      MergeCompleted(bot: PKV.Pkv, slack: uint64)
    | SlackExhausted(bot: PKV.Pkv, end: uint64, slack: uint64)
  
  method MergeToOneChild(top: PKV.Pkv, from: uint64, to: uint64, bot: PKV.Pkv, slack: uint64)
    returns (result: SingleMergeResult)
    requires PKV.WF(top)
    requires PKV.WF(bot)
    requires PKV.Keyspace.IsStrictlySorted(PSA.I(top.keys))
    requires PKV.Keyspace.IsStrictlySorted(PSA.I(bot.keys))
    requires to as nat - from as nat + PKV.NumKVPairs(bot) as nat < Uint32UpperBound()
    requires PKV.WeightPkv(bot) as nat + slack as nat < Uint32UpperBound()
    requires from <= to <= PKV.NumKVPairs(top)
    ensures PKV.WF(result.bot)
    ensures result.slack <= PKV.WeightPkv(bot) + slack
    ensures PKV.WeightPkv(result.bot) <= PKV.WeightPkv(bot) + slack - result.slack
    ensures result.SlackExhausted? ==> from <= result.end < to
  {
    var maxkeys: uint32 := (to - from + PKV.NumKVPairs(bot)) as uint32;
    var maxkeyspace: uint32 := (PSA.psaTotalLength(bot.keys) + slack) as uint32;
    var maxmsgspace: uint32 := (PSA.psaTotalLength(bot.messages) + slack) as uint32;
    var cap := Capacity(maxkeys, maxkeyspace, maxmsgspace);
    var dresult := new DynamicPkv.PreSized(cap);

    var runningSlack := slack;
    var topidx: uint64 := from;
    var botidx: uint64 := 0;

    assert PKV.Keyspace.IsStrictlySorted(PSA.I(dresult.keys.toPsa())) by {
      PKV.Keyspace.reveal_IsStrictlySorted();
    }

    assume false; // TODO(robj)
    
    while
      && topidx < to
      && botidx < PKV.NumKVPairs(bot)
      invariant from <= topidx <= to
      invariant botidx <= PKV.NumKVPairs(bot)
      invariant dresult.keys.nstrings <= botidx + topidx - from
      invariant runningSlack <= slack
      invariant dresult.WF()
      invariant dresult.weight() <= PKV.WeightPkv(PKV.subPkv(bot, 0, botidx)) + slack - runningSlack
      invariant fresh(dresult.Repr)
      invariant 0 < |PSA.I(dresult.keys.toPsa())| && topidx < to ==>
        PKV.Keyspace.lt(Seq.Last(PSA.I(dresult.keys.toPsa())), PSA.I(top.keys)[topidx])
      invariant 0 < |PSA.I(dresult.keys.toPsa())| && botidx as nat < |PSA.I(bot.keys)| ==>
        PKV.Keyspace.lt(Seq.Last(PSA.I(dresult.keys.toPsa())), PSA.I(bot.keys)[botidx])
      invariant PKV.Keyspace.IsStrictlySorted(PSA.I(dresult.keys.toPsa()))
      decreases to - topidx + PSA.psaNumStrings(bot.keys) - botidx
    {
      var topkey := PKV.GetKey(top, topidx);
      var botkey := PKV.GetKey(bot, botidx);
      var topmsg := PSA.psaElement(top.messages, topidx);
      var botmsg := PSA.psaElement(bot.messages, botidx);
      assert botmsg == PSA.I(bot.messages)[botidx];
      assert topmsg == PSA.I(top.messages)[topidx];
      
      if botidx as nat + 1 < |PSA.I(bot.keys)| {
        PKV.Keyspace.IsStrictlySortedImpliesLt(PSA.I(bot.keys), botidx as nat, botidx as nat + 1);
      }
      if topidx + 1 < to {
        PKV.Keyspace.IsStrictlySortedImpliesLt(PSA.I(top.keys), topidx as nat, topidx as nat + 1);
      }
      PSA.psaAppendIAppend(dresult.keys.toPsa(), PSA.I(bot.keys)[botidx]);
      PKV.Keyspace.StrictlySortedAugment(PSA.I(dresult.keys.toPsa()), PSA.I(bot.keys)[botidx]);
      if PSA.psaCanAppend(dresult.keys.toPsa(), PSA.I(top.keys)[topidx]) {
        PSA.psaAppendIAppend(dresult.keys.toPsa(), PSA.I(top.keys)[topidx]);
        PKV.Keyspace.StrictlySortedAugment(PSA.I(dresult.keys.toPsa()), PSA.I(top.keys)[topidx]);
      }

      var c := PKV.KeyspaceImpl.cmp(botkey, topkey);

      if c < 0 {
        var botmsg := PSA.psaElement(bot.messages, botidx);
        dresult.AppendEncodedMessage(botkey, botmsg);
        // no change is slack
        botidx := botidx + 1;
      } else if c > 0 {
        var topmsg := PSA.psaElement(top.messages, topidx);
        var kvweight := 4 + |topkey| as uint64 + 4 + |topmsg| as uint64;
        if kvweight < runningSlack {
          dresult.AppendEncodedMessage(topkey, topmsg);
          runningSlack := runningSlack - kvweight;
          topidx := topidx + 1;
        } else {
          break;
        }
      } else {
        var botmsg := PKV.GetMessage(bot, botidx);
        var topmsg := PKV.GetMessage(top, topidx);
        var newmsg := ValueMessage.Merge(topmsg, botmsg);
        var encoded_newmsg := PKV.Message_to_bytestring(newmsg);
        var kvweight := 4 + |topkey| as uint64 + 4 + |encoded_newmsg| as uint64;
        if newmsg != IdentityMessage() {
          var kvweight := 4 + |topkey| as uint64 + 4 + |encoded_newmsg| as uint64;
          if kvweight < runningSlack {
            dresult.AppendEncodedMessage(topkey, encoded_newmsg);
            runningSlack := runningSlack - kvweight;
          } else {
            break;
          }
        } else {
          var kvweight := 4 + |botkey| as uint64 + 4 + |PSA.psaElement(bot.messages, botidx)| as uint64;
          runningSlack := runningSlack + kvweight;
        }
        topidx := topidx + 1;
        botidx := botidx + 1;
      }
    }

    while topidx < to
      invariant from <= topidx <= to
      invariant dresult.WF()
      invariant dresult.keys.nstrings <= botidx + topidx - from
      invariant runningSlack <= slack
      invariant dresult.keys.nstrings <= botidx + topidx - from
      invariant dresult.weight() <= PKV.WeightPkv(PKV.subPkv(bot, 0, botidx)) + slack - runningSlack
      invariant fresh(dresult.Repr)
      invariant 0 < |PSA.I(dresult.keys.toPsa())| && topidx < to ==>
        PKV.Keyspace.lt(Seq.Last(PSA.I(dresult.keys.toPsa())), PSA.I(top.keys)[topidx])
      invariant PKV.Keyspace.IsStrictlySorted(PSA.I(dresult.keys.toPsa()))
    {
      var topkey := PKV.GetKey(top, topidx);
      var topmsg := PSA.psaElement(top.messages, topidx);
      var kvweight := 4 + |topkey| as uint64 + 4 + |topmsg| as uint64;
      assert topmsg == PSA.I(top.messages)[topidx];
      if topidx + 1 < to {
        PKV.Keyspace.IsStrictlySortedImpliesLt(PSA.I(top.keys), topidx as nat, topidx as nat + 1);
      }
      if PSA.psaCanAppend(dresult.keys.toPsa(), PSA.I(top.keys)[topidx]) {
        PSA.psaAppendIAppend(dresult.keys.toPsa(), PSA.I(top.keys)[topidx]);
        PKV.Keyspace.StrictlySortedAugment(PSA.I(dresult.keys.toPsa()), PSA.I(top.keys)[topidx]);
      }
      if kvweight < runningSlack {
        dresult.AppendEncodedMessage(topkey, topmsg);
        runningSlack := runningSlack - kvweight;
        topidx := topidx + 1;
      } else {
        break;
      }
    }

    while botidx < PKV.NumKVPairs(bot)
      invariant botidx <= PKV.NumKVPairs(bot)
      invariant dresult.WF()
      invariant dresult.keys.nstrings <= botidx + topidx - from
      invariant runningSlack <= slack
      invariant dresult.keys.nstrings <= botidx + topidx - from
      invariant dresult.weight() <= PKV.WeightPkv(PKV.subPkv(bot, 0, botidx)) + slack - runningSlack
      invariant fresh(dresult.Repr)
      invariant 0 < |PSA.I(dresult.keys.toPsa())| && botidx as nat < |PSA.I(bot.keys)| ==>
        PKV.Keyspace.lt(Seq.Last(PSA.I(dresult.keys.toPsa())), PSA.I(bot.keys)[botidx])
      invariant PKV.Keyspace.IsStrictlySorted(PSA.I(dresult.keys.toPsa()))
    {
      var botkey := PKV.GetKey(bot, botidx);
      var botmsg := PSA.psaElement(bot.messages, botidx);
      assert botmsg == PSA.I(bot.messages)[botidx];
      if botidx as nat + 1 < |PSA.I(bot.keys)| {
        PKV.Keyspace.IsStrictlySortedImpliesLt(PSA.I(bot.keys), botidx as nat, botidx as nat + 1);
      }
      PSA.psaAppendIAppend(dresult.keys.toPsa(), PSA.I(bot.keys)[botidx]);
      PKV.Keyspace.StrictlySortedAugment(PSA.I(dresult.keys.toPsa()), PSA.I(bot.keys)[botidx]);
      dresult.AppendEncodedMessage(botkey, botmsg);
      // no change in slack
      botidx := botidx + 1;
    }

    if topidx == to {
      result := MergeCompleted(dresult.toPkv(), runningSlack);
    } else {
      result := SlackExhausted(dresult.toPkv(), topidx, runningSlack);
    }
  }

  datatype MergeResult = MergeResult(top: PKV.Pkv, bots: seq<PKV.Pkv>, slack: uint64)
  
  method DoMergeToChildren(top: PKV.Pkv, pivotIdxs: seq<uint64>, bots: seq<PKV.Pkv>, slack: uint64) returns (result: MergeResult)
    requires PKV.WF(top)
    requires Uint64_Order.IsSorted(pivotIdxs)
    requires 0 < |bots| == |pivotIdxs| < Uint64UpperBound()
    requires Seq.Last(pivotIdxs) <= PKV.NumKVPairs(top)
    requires forall i | 0 <= i < |bots| :: PKV.WF(bots[i])
  {
    var tmp: SingleMergeResult;
    var runningSlack: uint64 := slack;
    var results := new PKV.Pkv[|bots| as uint64];

    assume false; // TODO(robj)

    Uint64_Order.IsSortedImpliesLte(pivotIdxs, 0, |pivotIdxs|-1);
    tmp := MergeToOneChild(top, 0, pivotIdxs[0], bots[0], runningSlack);
    results[0] := tmp.bot;
    runningSlack := tmp.slack;
    
    var i: uint64 := 1;
    while i < |bots| as uint64
      invariant i <= |bots| as uint64
      invariant tmp.SlackExhausted? ==> tmp.end < PKV.NumKVPairs(top)
    {
      Uint64_Order.IsSortedImpliesLte(pivotIdxs, i as int - 1, i as int);
      Uint64_Order.IsSortedImpliesLte(pivotIdxs, i as int, |pivotIdxs|-1);
      if tmp.MergeCompleted? {
        tmp := MergeToOneChild(top, pivotIdxs[i-1], pivotIdxs[i], bots[i], runningSlack);
        results[i] := tmp.bot;
        runningSlack := tmp.slack;
      } else {
        // Once we exhaust our slack on one child, we just copy the
        // remaining children
        //
        // XXX/FIXME/TODO[robj]: Do we want to copy the pkvs in this
        // situation?  I suspect not.
        results[i] := bots[i];
      }
      i := i + 1;
    }

    if tmp.SlackExhausted? {
      var leftover_top := PKV.SubPkv(top, tmp.end, PKV.NumKVPairs(top));
      result := MergeResult(leftover_top, results[..], runningSlack);
    } else {
      result := MergeResult(PKV.EmptyPkv(), results[..], runningSlack);
    }
  }

  method MergeToChildren(top: PKV.Pkv, pivots: seq<Key>, bots: seq<PKV.Pkv>, slack: uint64) returns (result: MergeResult)
    requires PKV.WF(top)
    requires PKV.Keyspace.IsStrictlySorted(PSA.I(top.keys))
    requires PKV.Keyspace.IsStrictlySorted(pivots)
    requires 0 < |bots| == |pivots| + 1 < Uint64UpperBound()
    requires forall i | 0 <= i < |bots| :: PKV.WF(bots[i])
  {
    var pivotIdxs := PSA.PivotIndexes(top.keys, pivots);
    forall i, j | 0 <= i <= j < |pivotIdxs|
      ensures pivotIdxs[i] <= pivotIdxs[j]
    {
      if j < |pivotIdxs|-1 {
        PKV.Keyspace.IndexOfFirstGteIsOrderPreserving(PSA.I(top.keys), pivots[i], pivots[j]);
      } else {
      }
    }
    assert Uint64_Order.IsSorted(pivotIdxs) by {
      Uint64_Order.reveal_IsSorted();
    }
    result := DoMergeToChildren(top, pivotIdxs, bots, slack);
  }
}

