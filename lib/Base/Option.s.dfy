module {:extern} Options {
  datatype Option<V> = None | Some(value:V)

  function MapOption<V0, V1>(opt: Option<V0>, f: V0 ~> V1) : (result: Option<V1>)
  requires opt.Some? ==> f.requires(opt.value)
  ensures opt.Some? <==> result.Some?
  ensures result.Some? ==> result.value == f(opt.value)
  reads if opt.Some? then f.reads(opt.value) else {}
  {
    match opt {
      case Some(v) => Some(f(v))
      case None => None
    }
  }

  function FlatMapOption<V0, V1>(opt: Option<V0>, f: V0 ~> Option<V1>) : (result: Option<V1>)
  requires opt.Some? ==> f.requires(opt.value)
  ensures opt.Some? && f(opt.value).Some? ==> result.Some?
  ensures opt.Some? && f(opt.value).Some? ==> result.value == f(opt.value).value
  reads if opt.Some? then f.reads(opt.value) else {}
  {
    match opt {
      case Some(v) => f(v)
      case None => None
    }
  }
} // module
