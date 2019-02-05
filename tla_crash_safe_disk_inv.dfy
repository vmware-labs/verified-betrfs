include "abstract_map.dfy"
include "tla_crash_safe_disk.dfy"

module LogInvariants {
import opened AppTypes
import opened LogImpl
import AbstractMap

predicate DiskLogPlausible(k:Disk.Constants, s:Disk.Variables)
{
    && 1 <= k.size
    && Disk.WF(k, s)
    && 1 <= DiskLogAddr(DiskLogSize(k, s)) <= k.size
}

predicate LogSizeValid(k:Constants, s:Variables)
{
    && 1 <= k.disk.size
    && Disk.WF(k.disk, s.disk)
    && (
        !s.mode.Reboot? ==>
            && s.diskCommittedSize == DiskLogSize(k.disk, s.disk)
            && DiskLogAddr(s.diskCommittedSize) <= DiskLogAddr(s.diskPersistedSize)
            && DiskLogAddr(s.diskPersistedSize) <= k.disk.size
       )
}

predicate LogPrefixAgrees(k:Constants, s:Variables)
{
    s.mode.Running? ==>
        && s.diskPersistedSize <= |s.memlog|
        && LogSizeValid(k, s)
        && (forall i :: 0 <= i < s.diskPersistedSize ==>
            Disk.Peek(k.disk, s.disk, DiskLogAddr(i), s.memlog[i]))
}

predicate ScanInv(k:Constants, s:Variables)
{
    s.mode.Recover? ==>
        && s.mode.next == |s.memlog|
        && s.diskCommittedSize == s.diskPersistedSize
        && s.mode.next <= s.diskCommittedSize
        && (forall i :: 0 <= i < |s.memlog| ==>
            Disk.Peek(k.disk, s.disk, DiskLogAddr(i), s.memlog[i]))
        //XXX && |s.memlog| <= s.diskPersistedSize
}

predicate Inv(k:Constants, s:Variables)
{
    && DiskLogPlausible(k.disk, s.disk)
    && LogSizeValid(k, s)
    && ScanInv(k, s)
    && LogPrefixAgrees(k, s)
}

lemma InvHoldsInit(k:Constants, s:Variables)
    requires Init(k, s)
    ensures Inv(k, s)
{
}

lemma InvHoldsInduction(k:Constants, s:Variables, s':Variables)
    requires Inv(k, s)
    requires Next(k, s, s')
    ensures Inv(k, s')
{
}

} // module LogImpl


