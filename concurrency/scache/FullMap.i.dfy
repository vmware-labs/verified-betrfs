module FullMaps {
  predicate IsFull<K(!new), V>(m: imap<K, V>) {
    forall k :: k in m
  }

  type FullMap<K(!new), V> = m : imap<K, V> | IsFull(m)
    witness *

  function zero_map<A(!new)>() : imap<A, nat> {
    imap k | true :: 0
  }

  function unit_fn<A(!new)>(a: A) : FullMap<A, nat> {
    imap k | true :: (if k == a then 1 else 0)
  }

  function add_fns<A(!new)>(f: FullMap<A, nat>, g: FullMap<A, nat>) : FullMap<A, nat> {
    imap b | true :: f[b] + g[b]
  }

  function SumFilter<A(!new)>(fn: (A) -> bool, f: FullMap<A, nat>) : nat

  lemma SumFilterSimp<A>()
  ensures forall fn: (A) -> bool, f: FullMap<A, nat>, g: FullMap<A, nat>
      {:trigger SumFilter(fn, add_fns(f, g)) } ::
      SumFilter(fn, add_fns(f, g)) == SumFilter(fn, f) + SumFilter(fn, g)

  ensures forall fn: (A) -> bool, x: A
      {:trigger SumFilter(fn, unit_fn(x)) } ::
      SumFilter(fn, unit_fn(x)) == (if fn(x) then 1 else 0)

  ensures forall fn: (A) -> bool
      {:trigger SumFilter(fn, zero_map()) } ::
      SumFilter(fn, zero_map()) == 0
  {
  }

  lemma UseZeroSum<A(!new)>(fn: (A) -> bool, f: FullMap<A, nat>)
  requires SumFilter(fn, f) == 0
  ensures forall x :: fn(x) ==> f[x] == 0
  {
  }
}
