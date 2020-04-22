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
  import opened ValueMessage
  import BW = BucketWeights
  
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

  // lemma SizeOfV_WeightBucket(pkv: Pkv)
  //   requires WF(pkv)
  //   requires Keyspace.IsStrictlySorted(PSA.I(pkv.keys))
  //   ensures SizeOfV(toVal(pkv)) == 16 + BW.WeightBucket(I(pkv))
  // {
  //   assume false;
  // }
  
  method ComputeWF(pkv: Pkv) returns (result: bool)
    requires PSA.WF(pkv.keys)
    requires PSA.WF(pkv.messages)
    ensures result == WF(pkv)
  {
    var vkl := ComputeValidStringLens(pkv.keys, KeyType.MaxLen());
    var vml := ComputeValidStringLens(pkv.messages, ValueType.MaxLen());
    assume IdentityMessage() !in IMessages(pkv.messages); // FIXME(robj): can we eliminate this from WF()?
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

}
