module LinearOption {
  linear datatype lOption<V> = lNone | lSome(linear value: V)

  function MapLOption<V0, V1>(opt: lOption<V0>, f: V0 ~> V1) :
    (result: lOption<V1>)
  requires opt.lSome? ==> f.requires(opt.value)
  ensures opt.lSome? <==> result.lSome?
  ensures result.lSome? ==> result.value == f(opt.value)
  reads if opt.lSome? then f.reads(opt.value) else {}
  {
    match opt {
      case lSome(v) => lSome(f(v))
      case lNone => lNone
    }
  }
}
