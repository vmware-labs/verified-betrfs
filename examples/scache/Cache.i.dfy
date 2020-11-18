module CacheImpl {
  datatype Cache = Cache(
    data: seq<Ptr>,
    status: seq<AtomicStatus>,
    read_locks: seq<seq<AtomicRefcount>
  )
}
