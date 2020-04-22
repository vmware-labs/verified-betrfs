include "../Base/Option.s.dfy"
include "../Marshalling/GenericMarshalling.i.dfy"
include "PackedStringArray.i.dfy"

module PackedStringArrayMarshalling {
  import opened Options
  import opened PackedStringArray
  import opened GenericMarshalling
  import Uint32_Order
  import opened NativeTypes
  
  function method grammar() : G
  ensures ValidGrammar(grammar())
  {
    GTuple([
      GUint32Array, // offsets
      GByteArray    // string bytes
    ])
  }

  function  fromVal(v: V) : (opsa: Option<Psa>)
    requires ValInGrammar(v, grammar())
    ensures opsa.Some? ==> WF(opsa.value)
  {
    assert ValInGrammar(v.t[0], GUint32Array);
    assert ValInGrammar(v.t[1], GByteArray);
    var offsets := v.t[0].va;
    var data := v.t[1].b;
    var psa := Psa(offsets, data);
    if WF(psa) then
      Some(psa)
    else
      None
  }
  
  function toVal(psa: Psa) : (v: V)
    requires WF(psa)
    ensures ValInGrammar(v, grammar())
  {
    VTuple([VUint32Array(psa.offsets), VByteArray(psa.data)])
  }

  lemma parseMarshalledCorrect(psa: Psa)
    requires WF(psa)
    ensures fromVal(toVal(psa)) == Some(psa)
  {
  }
  
  method ComputeWF(psa: Psa) returns (result: bool)
    requires |psa.offsets| < Uint64UpperBound()
    requires |psa.data| < Uint64UpperBound()
    ensures result == WF(psa)
  {
    var sorted := Uint32_Order.ComputeIsSorted(psa.offsets);
    var validLens := CheckStringLengths(psa.offsets);
    result :=
      && |psa.offsets| as uint64 < 0x1_0000_0000
      && |psa.data| as uint64 < 0x1_0000_0000
      && (|psa.offsets| as uint64 == 0 ==> |psa.data| as uint64 == 0)
      && (0 < |psa.offsets| as uint64 ==> |psa.data| as uint32 == psa.offsets[|psa.offsets| as uint64 - 1])
      && sorted
      && validLens;
  }
  
  method FromVal(v: V) returns (psa: Option<Psa>)
    requires ValidVal(v)
    requires ValInGrammar(v, grammar())
    ensures psa == fromVal(v)
  {
    assert ValInGrammar(v.t[0], GUint32Array);
    assert ValInGrammar(v.t[1], GByteArray);
    var offsets := v.t[0].va;
    var data := v.t[1].b;
    assert ValidVal(v.t[0]);
    assert ValidVal(v.t[1]);
    var tmp := Psa(offsets, data);
    var wf := ComputeWF(tmp);
    if wf {
      psa := Some(tmp);
    } else {
      psa := None;
    }
  }

  method ToVal(psa: Psa) returns (v: V)
    requires WF(psa)
    ensures ValInGrammar(v, grammar())
    ensures ValidVal(v)
    ensures v == toVal(psa)
  {
    v := VTuple([VUint32Array(psa.offsets), VByteArray(psa.data)]);
  }

}
