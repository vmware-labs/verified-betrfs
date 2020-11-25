module Refcounter {
  linear datatype Refcounter<V> = Refcounter<V>(value: G, count: int)

  function method {:extern} wrap<V>(linear v: V) : (linear rc: RefCounter<V>)
  ensures rc.value == v
  ensures rc.count == 0

  function method {:extern} unwrap<V>(linear rc: RefCounter<V>) : (linear v: V)
  requires rc.count == 0
  ensures v == rc.value

  function method {:extern} get_read<V>(linear rc: RefCounter<V>)
      : (linear rc': RefCounter<V>, readonly linear v: Value)
  ensures rc'.count == rc.count + 1
  ensures rc'.value == rc.value
  ensures v == rc.value

  function method {:extern} return_read<V>(linear rc: RefCounter<V>,
          readonly linear v: Value)
      : (linear rc': RefCounter<V>)
  requires v == rc.value
  ensures rc'.count == rc.count - 1
  ensures rc'.value == rc.value
}
