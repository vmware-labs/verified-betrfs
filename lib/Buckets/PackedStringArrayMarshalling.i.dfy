include "../Base/Option.s.dfy"
include "../Marshalling/GenericMarshalling.i.dfy"
include "PackedStringArray.i.dfy"

module PackedStringArrayMarshalling {
  import opened Options
  import opened PackedStringArray
  import opened GenericMarshalling

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
    ensures fromVal(v) == Some(psa)
  {
    VTuple([VUint32Array(psa.offsets), VByteArray(psa.data)])
  }

  method computeWF(psa: Psa) return (result: bool)
    ensures result == WF(psa)
  {
    
  }
  
  method fromVal(v: V)
    returns (psa: Option<Psa>)
    requires ValInGrammar(v, grammar())
    ensures psa.Some? ==> WF(psa.value)
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

  // method ToVal(psa: Psa)
  //   returns (v: V)
  //   requires WF(psa)
  //   ensures ValInGrammar(v, grammar())
  //   ensures v == Val(psa)
  // {
  //   v := VTuple([VUint32Array(psa.offsets), VByteArray(psa.data)]);
  // }

}
