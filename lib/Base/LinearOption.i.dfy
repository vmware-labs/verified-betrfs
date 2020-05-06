include "Option.s.dfy"

module LinearOption {
  import opened Options

  linear datatype TupleResult<V> = TupleResult(linear result: lOption<V>, linear other: lOption<V>)

  linear datatype lOption<V> = lNone | lSome(linear value: V)
  {
    function Map<V1>(f: V ~> V1) : (result: lOption<V1>)
    requires this.lSome? ==> f.requires(this.value)
    ensures this.lSome? <==> result.lSome?
    ensures result.lSome? ==> result.value == f(this.value)
    reads if this.lSome? then f.reads(this.value) else {}
    {
      match this {
        case lSome(v) => lSome(f(v))
        case lNone => lNone
      }
    }

    function Option() : (result: Option<V>)
    {
      match this {
        case lSome(v) => Some(v)
        case lNone => None
      }
    }
  }
}

module Test {
  import opened LinearOption
  function Something(a: lOption<int>): lOption<int>
  ensures a.lSome? ==> Something(a).lSome? && Something(a).value == a.value * 2
  {
    a.Map(x => x * 2)
  }
}
