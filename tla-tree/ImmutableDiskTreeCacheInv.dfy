include "CrashableMap.dfy"
include "ImmutableDiskTreeInterpretation.dfy"

module ImmutableDiskTreeCacheInv {
import opened KVTypes
import opened TreeTypes
import ImmutableDiskTreeImpl
import opened ImmutableDiskTree
import opened ImmutableDiskTreeInv
import opened ImmutableDiskTreeHeight
import opened ImmutableDiskTreeContent
import opened ImmutableDiskTreeInterpretation

predicate ValidCacheIndex(k:Constants, lba:TreeDisk.LBA)
{
    0 <= lba < Impl.DiskSize(k.impl)
}

predicate ValidCacheIndicesInv(k:Constants, s:Variables)
{
    forall lba :: lba in s.impl.cache ==> ValidCacheIndex(k, lba)
}

predicate CleanCacheSectorsMatchDiskInv(k:Constants, s:Variables)
    requires WFConstants(k)
    requires TreeDisk.WF(k.disk, s.disk)
    requires ValidCacheIndicesInv(k, s)
{
    forall lba :: lba in s.impl.cache && s.impl.cache[lba].state.Clean?
        ==> s.impl.cache[lba].sector == s.disk.sectors[lba]
}

} // module
