include "../../lib/Lang/NativeTypes.s.dfy"

module {:extern "ThreadUtils"} ThreadUtils {
  import opened NativeTypes

  method {:extern} sleep(ns: uint64)
  method {:extern} pause()
}
