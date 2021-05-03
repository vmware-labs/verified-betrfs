module FullMaps {
  predicate IsFull<K(!new), V>(m: imap<K, V>) {
    forall k :: k in m
  }

  type FullMap<K(!new), V> = m : imap<K, V> | IsFull(m)
    witness *

  function zero_map<A(!new)>() : imap<A, nat> {
    imap k | true :: 0
  }

  function add_fns<A(!new)>(f: FullMap<A, nat>, g: FullMap<A, nat>) : FullMap<A, nat> {
    imap b | true :: f[b] + g[b]
  }
}
