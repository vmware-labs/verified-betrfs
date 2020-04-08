include "../Lang/NativeTypes.s.dfy"

module SeqComparison {
  import opened NativeTypes

  // This was moved out of total_order.i.dfy because it's a .i file.
  // We need use this definition for some spec things (e.g., successor queries)

  predicate {:opaque} lte(a: seq<byte>, b: seq<byte>)
  decreases |a|
  {
    if |a| == 0 then (
      true
    ) else (
      if |b| == 0 then (
        false
      ) else (
        if a[0] < b[0] then true
        else if b[0] < a[0] then false
        else lte(a[1..], b[1..])
      )
    )
  }

  predicate lt(a: seq<byte>, b: seq<byte>)
  {
    lte(a, b) && a != b
  }
}
