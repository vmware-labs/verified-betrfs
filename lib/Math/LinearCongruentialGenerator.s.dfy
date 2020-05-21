include "../Base/NativeTypes.s.dfy"

module {:extern} LinearCongruentialGenerator {
  import opened NativeTypes

  class {:extern} LCG {
    constructor {:extern} (seed: uint64)

    method {:extern} next() returns (val: uint64)
    modifies this
  }
}
