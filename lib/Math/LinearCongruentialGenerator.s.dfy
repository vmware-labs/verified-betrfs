include "../Base/NativeTypes.s.dfy"

module {:extern} LinearCongruentialGenerator {
  import opened NativeTypes

  method {:extern} steadyClockMillis() returns (millis: uint64)
  method {:extern} opaqueBlackhole(value: uint64)

  class {:extern} LCG {
    constructor {:extern} (seed: uint64)

    method {:extern} next() returns (val: uint64)
    modifies this
  }

}
