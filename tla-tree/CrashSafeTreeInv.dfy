include "CrashSafeTree.dfy"

module CrashSafeTreeInv {
import opened CrashSafeTree

predicate IsNodeStorage(lba:LBA, virgin:int)  // Trigger target.
{
    1 <= lba < virgin
}

predicate MinimalDisk(k:Constants)
{
    2 <= k.disk.size
}

predicate UsedSpaceFitsOnDisk(k:Constants, s:Variables, virgin:int)
    requires TreeDisk.WF(k.disk, s.disk)
    requires MinimalDisk(k)
{
    virgin <= k.disk.size
}

predicate IsNotSuperblock(k:Constants, s:Variables, virgin:int, lba:LBA)    // Trigger target
    requires TreeDisk.WF(k.disk, s.disk)
    requires MinimalDisk(k)
    requires UsedSpaceFitsOnDisk(k, s, virgin)
    requires IsNodeStorage(lba, virgin)
{
    !TreeDisk.PeekF(k.disk, s.disk, lba).Superblock?
}

predicate StorageIsNotSuperblocks(k:Constants, s:Variables, virgin:int)
    requires TreeDisk.WF(k.disk, s.disk)
    requires MinimalDisk(k)
    requires UsedSpaceFitsOnDisk(k, s, virgin)
{
    forall lba :: IsNodeStorage(lba, virgin) ==> IsNotSuperblock(k, s, virgin, lba)
}

predicate DiskStructureInv(k:Constants, s:Variables)
{
    && TreeDisk.WF(k.disk, s.disk)
    && MinimalDisk(k)

    && 1 <= k.disk.size // Gotta have room for a superblock!
    && var super := TreeDisk.PeekF(k.disk, s.disk, SUPERBLOCK_LBA());
    && super.Superblock?
    && UsedSpaceFitsOnDisk(k, s, super.virgin)
    && StorageIsNotSuperblocks(k, s, super.virgin)
}

predicate CacheEntryReflectsDisk(k:Constants, s:Variables, lba:LBA)
    requires TreeDisk.WF(k.disk, s.disk)
    requires lba in s.cache
{
    && TreeDisk.ValidLBA(k.disk, lba)
    && s.cache[lba] == TreeDisk.PeekF(k.disk, s.disk, lba)
}

predicate CacheReflectsDisk(k:Constants, s:Variables)
    requires TreeDisk.WF(k.disk, s.disk)
{
    forall lba :: lba in s.cache ==> CacheEntryReflectsDisk(k, s, lba)
}

predicate VirginExcludesSuperblock(k:Constants, s:Variables)
    requires DiskStructureInv(k, s) // get a well-formed, nonempty disk
{
    && var super := TreeDisk.PeekF(k.disk, s.disk, SUPERBLOCK_LBA());
    && 2 <= super.virgin
}

predicate Inv(k:Constants, s:Variables)
{
    && TreeDisk.WF(k.disk, s.disk)
    && MinimalDisk(k)
    && DiskStructureInv(k, s)
    && CacheReflectsDisk(k, s)
    && VirginExcludesSuperblock(k, s)
}

lemma CanAllocateImpliesNotSuperblock(k:Constants, s:Variables, super:Sector, childRead:NRead)
    requires Inv(k, s)
    requires CanAllocate(k, s, super, childRead)
    ensures childRead.lba != SUPERBLOCK_LBA();
{
    if NodeDisconnected(k, s, childRead) {
        assert childRead.lba != SUPERBLOCK_LBA();
    } else if NodeIsCold(k, s, childRead.lba, TreeDisk.NodeSector(childRead.node)) {
        assert childRead.lba != SUPERBLOCK_LBA();
    } else {
        assert SectorIsVirgin(k, s, super, childRead.lba);
        assert childRead.lba != SUPERBLOCK_LBA();
    }
}

lemma InvHoldsInit(k:Constants, s:Variables)
    requires Init(k, s)
    ensures Inv(k, s)
{
/*
    var super := TreeDisk.PeekF(k.disk, s.disk, SUPERBLOCK_LBA());
    forall lba | IsNodeStorage(lba, super.virgin)
        ensures !TreeDisk.PeekF(k.disk, s.disk, lba).Superblock?
    {
        assert lba == 1;
    }
*/
}

lemma InvHoldsInduction(k:Constants, s:Variables, s':Variables)
    requires Inv(k, s)
    requires Next(k, s, s')
    ensures Inv(k, s')
{
    var step :| NextStep(k, s, s', step);
    match step {
        case CacheFaultActionStep(lba, sector) => {
            assert DiskStructureInv(k, s');
        }
        case CacheEvictActionStep(lba) => {
            assert DiskStructureInv(k, s');
        }
        case PrepareGrowActionStep(super, parentRead, i, childRead) => {
            assert WriteThroughNode(k, s, s', childRead.lba, ChildNodeForParentIdx(parentRead, i));
            assert childRead.lba != SUPERBLOCK_LBA();
            assert DiskStructureInv(k, s');
        }
        case CommitGrowActionStep(parentRead, i, childRead) => {
            assert DiskStructureInv(k, s');
        }
        case ContractNodeActionStep(parentRead, i, childRead) => {
            assert DiskStructureInv(k, s');
        }
        case QueryActionStep(datum, lookup) => {
        }
        case InsertActionStep(datum, lookup) => {
            assert DiskStructureInv(k, s');
        }
        case DeleteActionStep(datum, lookup) => {
            assert DiskStructureInv(k, s');
        }
        case MoveToFreeListActionStep(childRead) => {
            assert DiskStructureInv(k, s');
        }
        case CommitFreeListActionStep(super) => {
        /*
            forall lba | IsNodeStorage(lba, super.virgin)
                ensures IsNotSuperblock(k, s', super.virgin, lba)
            {
            }
            assert StorageIsNotSuperblocks(k, s', super.virgin);
            assert DiskStructureInv(k, s');
            */
        }
        case WriteAnythingIntoVirginActionStep(super, lba, data) => {
        }
        case ExpandStorageActionStep(super, newVirgin, nreads) => {
            assert UsedSpaceFitsOnDisk(k, s', newVirgin);
            assert StorageIsNotSuperblocks(k, s', newVirgin);
            assert DiskStructureInv(k, s');
        }
    }
}

}
