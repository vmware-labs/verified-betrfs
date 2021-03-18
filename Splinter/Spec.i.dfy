include "Base.i.dfy"

module MapSpecMod {
  import InterpMod

  datatype Variables = Variables(interp: InterpMod.Interp)

  predicate Init(s: Variables)
  {
    && s.interp == Empty
  }

  predicate Put(s: Variables, s': Variables, k: Key, v: Value)
  {
    && s' == s.(interp := s.interp.mi[k := v], seqEnd := s.interp.seqEnd + 1)
      // NB mutations advance the sequence number
  }

  predicate Query(s: Variables, s': Variables, k: Key, v: Value)
  {
    && s.interp.mi[k] == v
    && s' == s
  }
}

module DeferredWriteMapSpecMod {
  import InterpMod
  import MapSpecMod

  datatype Variables = Variables(interp: InterpMod.Interp)

  predicate Init(s: Variables)
  {
    && s.interp == Empty
  }

  predicate Put(s: Variables, s': Variables, k: Key, v: Value)
  {
    && s' == s.(interp := s.interp.mi[k := v], seqEnd := s.interp.seqEnd + 1)
      // NB mutations advance the sequence number
  }

  predicate Query(s: Variables, s': Variables, k: Key, v: Value)
  {
    && s.interp.mi[k] == v
    && s' == s
  }
}
