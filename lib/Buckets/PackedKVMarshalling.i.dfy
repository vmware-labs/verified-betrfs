include "../Base/Option.s.dfy"
include "../Marshalling/GenericMarshalling.i.dfy"
include "PackedStringArrayMarshalling.i.dfy"
include "PackedKV.i.dfy"
include "BucketWeights.i.dfy"

module PackedKVMarshalling {
  import opened Options
  import PSA = PackedStringArray
  import opened GenericMarshalling
  import opened NativeTypes
  import PSAMarshalling = PackedStringArrayMarshalling
  import opened PackedKV
  import opened ValueMessage`Internal
  import ValueType`Internal
  import opened BucketsLib
  import BW = BucketWeights
  import Seq = Sequences
  
  function method grammar() : G
    ensures ValidGrammar(grammar())
  {
    GTuple([
      PSAMarshalling.grammar(), // keys
      PSAMarshalling.grammar()  // messages
    ])
  }

  function fromVal(v: V) : (opkv: Option<Pkv>)
    requires ValInGrammar(v, grammar())
    ensures opkv.Some? ==> WF(opkv.value)
  {
    var okeys := PSAMarshalling.fromVal(v.t[0]);
    var omsgs := PSAMarshalling.fromVal(v.t[1]);
    if okeys.Some? && omsgs.Some? then (
      var pkv := Pkv(okeys.value, omsgs.value);
      if WF(pkv) then
        Some(pkv)
      else
        None
    ) else
      None
  }

  function toVal(pkv: Pkv) : (v: V)
    requires WF(pkv)
    ensures ValInGrammar(v, grammar())
  {
    VTuple([PSAMarshalling.toVal(pkv.keys), PSAMarshalling.toVal(pkv.messages)])
  }

  lemma parseMarshalledCorrect(pkv: Pkv)
    requires WF(pkv)
    ensures fromVal(toVal(pkv)) == Some(pkv)
  {
  }

  lemma uniqueMarshalling(v: V)
    requires ValInGrammar(v, grammar())
    requires fromVal(v).Some?
    ensures toVal(fromVal(v).value) == v
  {
    PSAMarshalling.uniqueMarshalling(v.t[0]);
    PSAMarshalling.uniqueMarshalling(v.t[1]);
  }
  
  method CheckStringLengths(offsets: seq<uint32>) returns (b: bool)
    requires |offsets| < Uint64UpperBound()
    ensures b <==>
    (
    && (0 < |offsets| ==> offsets[0] as nat <= KeyType.MaxLen() as nat)
    && (forall i | 0 <= i < |offsets| - 1 :: offsets[i+1] as int - offsets[i] as int <= KeyType.MaxLen() as int)
    )
  {
    var i: uint64 := 0;

    if 0 < |offsets| as uint64 && offsets[0] as uint64 > KeyType.MaxLen() {
      return false;
    }

    if |offsets| as nat <= 1 {
      return true;
    }
    
    while i + 1 < |offsets| as uint64
      invariant i as nat + 1 <= |offsets|
      invariant forall j | 0 <= j < i :: offsets[j+1] as int - offsets[j] as int <= KeyType.MaxLen() as int
    {
      var oi: int64 := offsets[i] as int64;
      var oip1: int64 := offsets[i+1] as int64;
      if KeyType.MaxLen() as int64 < oip1 - oi {
        return false;
      }
      i := i + 1;
    }
    return true;
  }
  
  method ComputeWF(pkv: Pkv) returns (result: bool)
    requires PSA.WF(pkv.keys)
    requires PSA.WF(pkv.messages)
    ensures result == WF(pkv)
  {
    var vkl := ComputeValidStringLens(pkv.keys, KeyType.MaxLen());
    var vml := ComputeValidStringLens(pkv.messages, ValueType.MaxLen());
    assert IdentityMessage() !in IMessages(pkv.messages);
    result :=
      && PSA.psaNumStrings(pkv.keys) == PSA.psaNumStrings(pkv.messages)
      && vkl
      && vml;
    if result {
      assert WF(pkv);
    } else {
      assert !WF(pkv);
    }
  }
  
  method FromVal(v: V) returns (pkv: Option<Pkv>)
    requires ValInGrammar(v, grammar())
    requires ValidVal(v)
    ensures pkv == fromVal(v)
  {
    var okeys := PSAMarshalling.FromVal(v.t[0]);
    var omessages := PSAMarshalling.FromVal(v.t[1]);
    if okeys.Some? && omessages.Some? {
      var tmp := Pkv(okeys.value, omessages.value);
      var wf := ComputeWF(tmp);
      if wf {
        pkv := Some(tmp);
      } else {
        pkv := None;
      }
    } else {
      pkv := None;
    }
  }

  method ToVal(pkv: Pkv) returns (v: V)
    requires WF(pkv)
    ensures ValInGrammar(v, grammar())
    ensures v == toVal(pkv)
    ensures ValidVal(v)
  {
    var vkeys := PSAMarshalling.ToVal(pkv.keys);
    var vmessages := PSAMarshalling.ToVal(pkv.messages);
    v := VTuple([vkeys, vmessages]);
  }

  lemma PKVSizeOfV(pkv: Pkv)
    requires WF(pkv)
    ensures SizeOfV(toVal(pkv)) == 0
    + SizeOfV(PSAMarshalling.toVal(pkv.keys))
    + SizeOfV(PSAMarshalling.toVal(pkv.messages))
  {
    var v := toVal(pkv);
    var ov := v.t[0];
    var dv := v.t[1];
    calc {
      SizeOfV(v);
      { reveal_SeqSum(); }
      SizeOfV(ov) + SeqSum(v.t[1..]);
      { reveal_SeqSum(); }
      SizeOfV(ov) + SizeOfV(dv);
    }
  }

  lemma SizeOfVPackedStringArrayIsKeyListWeight(psa: PSA.Psa)
    requires PSA.WF(psa)
    requires ValidStringLens(PSA.I(psa), KeyType.MaxLen() as nat)
    ensures SizeOfV(PSAMarshalling.toVal(psa)) == BW.WeightKeyList(IKeys(psa)) + 2 * SizeOfV(VUint64(0))
    decreases |IKeys(psa)|
  {
    var keys := IKeys(psa);
    if |keys| == 0 {
    } else {
      var prepsa := PSA.psaDropLast(psa);
      var prekeys := IKeys(prepsa);
      var last := Seq.Last(keys);
      
      SizeOfVPackedStringArrayIsKeyListWeight(prepsa);
      assert keys == prekeys + [ Seq.Last(keys) ];
      BW.WeightKeyListPushBack(prekeys, Seq.Last(keys));
      PSAMarshalling.PSASizeOfV(psa);
      PSAMarshalling.PSASizeOfV(prepsa);
    }
  }
  
  lemma SizeOfVPackedStringArrayIsMessageListWeight(psa: PSA.Psa)
    requires PSA.WF(psa)
    requires ValueType.ValidMessageBytestrings(PSA.I(psa))
    ensures SizeOfV(PSAMarshalling.toVal(psa)) == BW.WeightMessageList(IMessages(psa)) + 2 * SizeOfV(VUint64(0))
    decreases |PSA.I(psa)|
  {
    var msgs := IMessages(psa);
    assert msgs == bytestringSeq_to_MessageSeq(PSA.I(psa));
    
    if |msgs| == 0 {
    } else {
      var prepsa := PSA.psaDropLast(psa);
      var premsgs := IMessages(prepsa);
      var last := Seq.Last(msgs);

      SizeOfVPackedStringArrayIsMessageListWeight(prepsa);
      bytestringSeq_to_MessageSeq_Additive(PSA.I(prepsa), [ Seq.Last(PSA.I(psa)) ]);
      assert msgs == premsgs + [ Seq.Last(msgs) ];
      BW.WeightMessageListPushBack(premsgs, Seq.Last(msgs));
      PSAMarshalling.PSASizeOfV(psa);
      PSAMarshalling.PSASizeOfV(prepsa);
    }
  }
  
  lemma SizeOfVPackedKVIsBucketWeight(pkv: PackedKV.Pkv)
    requires PackedKV.WF(pkv)
    ensures SizeOfV(toVal(pkv)) == BW.WeightBucket(PackedKV.I(pkv)) + 4 * SizeOfV(VUint64(0))
    decreases NumKVPairs(pkv)
  {
    SizeOfVPackedStringArrayIsKeyListWeight(pkv.keys);
    SizeOfVPackedStringArrayIsMessageListWeight(pkv.messages);
    PKVSizeOfV(pkv);
  }
}
