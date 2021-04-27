module FullMaps {
  predicate IsFull<K(!new), V>(m: imap<K, V>) {
    forall k :: k in m
  }

  type FullMap<K(!new), V> = m : imap<K, V> | IsFull(m)
    witness *
}
