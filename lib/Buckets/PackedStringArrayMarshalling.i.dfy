include "../Marshalling/GenericMarshalling.i.dfy"
include "PackedStringArray"

module PackedStringArrayMarshalling {
  import opened PackedStringArray
  import opened GenericMarshalling

  function method grammar() : G
  ensures ValidGrammar(PSAGrammar())
  {
    GTuple([
      GUint32Array, // offsets
      GbyteArray    // string bytes
    ])
  }

  method toVal(psa: PSA.Psa)
    returns (v: V)
    requires PSA.WF(psa)
    ensures ValidInGrammar(grammar(), v)
  {
    v := VTuple([VUint32Array(psa.offsets), VByteArray(psa.data)]);
  }

  method fromVal(v: V)
    returns (psa: PSA.Psa)
    requires ValidInGrammar(grammar(), v)
    ensures PSA.WF(psa)
  {
    v := VTuple([VUint32Array(psa.offsets), VByteArray(psa.data)]);
  }
}
