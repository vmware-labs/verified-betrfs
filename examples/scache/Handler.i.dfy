module Handler {
  linear datatype Handle = CacheEntryHandle(
      linear cache_entry: CacheResources.R,
      linear data: ArrayDeref<byte>,
      linear idx: Deref<int>
  )
  {
    predicate is_handle(key: Key)
    {
      && data.ptr == key.data_ptr
      && idx.ptr == key.idx_ptr
      && cache_entry.CacheEntry?
      && cache_entry.cache_idx == key.cache_idx
    }
  }

  linear datatype ConstHandle = ConstHandle(
      linear cache_entry: CacheResources.R, // TODO should be readonly
      linear data: ConstArrayDeref<byte>,
      linear idx: ConstDeref<int>
  )
  {
    predicate is_handle(key: Key)
    {
      && data.ptr == key.data_ptr
      && idx.ptr == key.idx_ptr
      && cache_entry.CacheEntry?
      && cache_entry.cache_idx == key.cache_idx
    }
  }

/*
  linear datatype CacheEntryStore = CacheEntryStore(
      cache_entry: CacheResources.R,
      refcounter: CacheEntryRefcount.R)

  linear datatype DataStore = DataStore(
      data: ConstArrayDeref<byte>,
      refcounter: ConstArrayRefcount.R)

  linear datatype IdxStore = IdxStore(
      data: ConstArrayDeref<byte>,
      refcounter: ConstRefcount.R)

  linear datatype State = State(
    linear rw: RWLockResource.R,
    linear handles: lmap<int, CacheEntryStore>,
    linear handles: lmap<int, CacheEntryStore>,
  )

  predicate InvKey(s: State, key: Key)
  {
    if key in s.handles 
  }

  predicate Inv(s: State)
  {
    forall key :: InvKey(s, key)
  }*/
}
