include "../../lib/Lang/NativeTypes.s.dfy"

module {:extern "ThreadUtils"} ThreadUtils {
  import opened NativeTypes

  method {:extern} thread_yield()
  method {:extern} sleep(ns: uint64)
}
