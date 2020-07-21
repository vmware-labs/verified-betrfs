module Inout {
  method {:axiom} Assign<V>(inout v: V, newV: V)
  ensures v == newV

  ghost method {:axiom} AssignGhost<V>(inout v: V, newV: V)
  ensures v == newV

  method {:axiom} Replace<V>(linear inout v: V, linear newV: V) returns (linear replaced: V)
  ensures v == newV
}
