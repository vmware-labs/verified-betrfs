module Inout {
  method {:axiom} Replace<V>(linear inout v: V, linear newV: V) returns (linear replaced: V)
  ensures v == newV
}
