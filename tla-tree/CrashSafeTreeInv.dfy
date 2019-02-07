include "CrashSafeTree.dfy"

module CrashSafeTreeInv {
import opened CrashSafeTree

predicate IsNodeStorage(lba:LBA, super:Sector)  // Trigger target.
    requires super.Superblock?
{
    1 <= lba < super.virgin
}

predicate MinimalDisk(k:Constants)
{
    2 <= k.disk.size
}

predicate DiskStructureInv(k:Constants, s:Variables)
    requires TreeDisk.WF(k.disk, s.disk)
    requires MinimalDisk(k)
{
    && 1 <= k.disk.size // Gotta have room for a superblock!
    && var super := TreeDisk.PeekF(k.disk, s.disk, SUPERBLOCK_LBA());
    && super.Superblock?
    && super.virgin <= k.disk.size   // used blocks fit on the disk
    && (forall lba :: IsNodeStorage(lba, super) ==>
            !TreeDisk.PeekF(k.disk, s.disk, lba).Superblock?
        )
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

predicate Inv(k:Constants, s:Variables)
{
    && TreeDisk.WF(k.disk, s.disk)
    && MinimalDisk(k)
    && DiskStructureInv(k, s)
    && CacheReflectsDisk(k, s)
}

lemma InvHoldsInit(k:Constants, s:Variables)
    requires Init(k, s)
    ensures Inv(k, s)
{
    var super := TreeDisk.PeekF(k.disk, s.disk, SUPERBLOCK_LBA());
    forall lba | IsNodeStorage(lba, super)
        ensures !TreeDisk.PeekF(k.disk, s.disk, lba).Superblock?
    {
        assert lba == 1;
    }
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
        case PrepareGrowActionStep(parentRead, i, childRead) => {
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
        case MoveToFreeListActionStep(lba, childRead) => {
            assert DiskStructureInv(k, s');
        }
        case CommitFreeListActionStep(super) => {
            assert DiskStructureInv(k, s');
        }
    }
}

}
