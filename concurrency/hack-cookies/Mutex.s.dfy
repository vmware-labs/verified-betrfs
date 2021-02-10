abstract module AbstractMutex {
  type ConstType
  type ValueType

  type OpaqueType
  datatype Mutex = Mutex(x: OpaqueType)
  {
    function {:axiom} constant() : ConstType
  }

  predicate Inv(k: ConstType, v: ValueType)

  method {:axiom} new_mutex(k: ConstType, linear v: ValueType)
  returns (m: Mutex)
  requires Inv(k, v)
  ensures m.constant() == k

  method {:axiom} acquire(m: Mutex)
  returns (linear v: ValueType)
  ensures Inv(m.constant(), v)

  // TODO enforce that the caller has called acquire previously
  method {:axiom} release(m: Mutex, linear v: ValueType)
  requires Inv(m.constant(), v)
}
