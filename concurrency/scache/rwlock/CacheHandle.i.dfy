include "../../framework/Ptrs.s.dfy"
include "../cache/CacheResources.i.dfy"
include "../Constants.i.dfy"
include "../../framework/Cells.s.dfy"

module CacheHandle {
  import opened Ptrs
  import opened Constants
  import opened GhostLoc
  import opened Cells
  import CacheResources
  import opened NativeTypes

  datatype Key = Key(
      data_ptr: Ptrs.Ptr,
      idx_cell: Cell<int64>,
      ghost cache_idx: nat)

  glinear datatype Handle =
    | CacheEmptyHandle(
        ghost key: Key,
        glinear cache_empty: CacheResources.CacheEmpty,
        glinear idx: CellContents<int64>,
        glinear data: PointsToArray<byte>)
    | CacheReadingHandle(
        ghost key: Key,
        glinear cache_reading: CacheResources.CacheReading,
        glinear idx: CellContents<int64>,
        glinear data: PointsToArray<byte>)
    | CacheEntryHandle(
        ghost key: Key,
        glinear cache_entry: CacheResources.CacheEntry,
        glinear idx: CellContents<int64>,
        glinear data: PointsToArray<byte>)
  {
    predicate is_handle(key: Key)
    {
      && this.key == key
      && this.idx.cell == key.idx_cell
      && this.data.ptr == key.data_ptr
      && |this.data.s| == 4096
      && 0 <= this.idx.v as int < NUM_DISK_PAGES as int

      && (this.CacheEmptyHandle? ==>
        && this.cache_empty.cache_idx == key.cache_idx
      )
      && (this.CacheReadingHandle? ==>
        && this.cache_reading.cache_idx == key.cache_idx
        && this.cache_reading.disk_idx == this.idx.v as int
      )
      && (this.CacheEntryHandle? ==>
        && this.cache_entry.cache_idx == key.cache_idx
        && this.cache_entry.disk_idx == this.idx.v as int
        && this.cache_entry.data == this.data.s
      )
    }
  }
}
