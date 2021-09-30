include "../../lib/Base/Option.s.dfy"

module GlinearOption {
  import opened Options

  glinear datatype glOption<V> = glNone | glSome(glinear value: V)

  function method unwrap_value<V>(glinear opt: glOption<V>) : glinear V
  requires opt.glSome?
  {
    glinear var glSome(v) := opt;
    v
  }

  glinear method dispose_glnone<V>(glinear opt: glOption<V>)
  requires opt.glNone?
  {
    glinear match opt {
      case glNone => { }
    }
  }
}
