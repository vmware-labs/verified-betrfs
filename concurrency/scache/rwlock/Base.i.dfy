include "../../framework/PCMWrap.s.dfy"
include "../../framework/Ptrs.s.dfy"
include "../CacheResources.i.dfy"
include "../Constants.i.dfy"

module RWLockBase refines PCMWrap {
  import opened Ptrs
  import opened Constants
  import CacheResources
  import opened NativeTypes

  datatype Key = Key(
      data_ptr: Ptrs.Ptr,
      idx_ptr: Ptrs.Ptr,
      cache_idx: int,
      cr_loc: Loc)

  glinear datatype Handle = CacheEntryHandle(
      ghost key: Key,
      glinear cache_entry: CacheResources.Token,
      glinear data: PointsToArray<byte>,
      glinear idx: PointsTo<int>)
  {
    predicate is_handle(key: Key)
    {
      && this.key == key
      && this.cache_entry.get()
          == CacheResources.CacheEntry(this.idx.v, key.cache_idx, this.data.s)
      && this.cache_entry.loc() == key.cr_loc
      && this.data.ptr == key.data_ptr
      && this.idx.ptr == key.idx_ptr
      && |this.data.s| == 4096
      && 0 <= this.idx.v < NUM_DISK_PAGES
    }
  }

  type G = Handle
}
