include "abstract_map.dfy"
include "tla_crash_safe_disk.dfy"

module RefinementProof {
import opened AppTypes
import opened LogImpl
import AbstractMap

// Find a key in a log-representation map
function {:opaque} ILogKey(log:seq<Datum>, k:int) : int
{
    if log==[]
    then
        AbstractMap.EmptyValue()
    else if log[|log|-1].key == k
    then
        log[|log|-1].value
    else
        ILogKey(log[..|log|-1], k)
}

// Interpret a log sequence of Datums as a map
function {:opaque} ILog(log:seq<Datum>) : imap<int, int>
{
    imap k | AbstractMap.InDomain(k) :: ILogKey(log, k)
}

// Interpret the ephemeral system state (memlog) as a map
function IEphemeral(k:Constants, s:Variables) : imap<int, int>
{
    ILog(s.memlog)
}

function {:opaque} DiskLogRecursive(k:Constants, s:Variables, len:nat) : seq<Datum>
    requires len+1 <= k.disk.size;
    requires Disk.WF(k.disk, s.disk);
{
    if len==0 
    then []
    else DiskLogRecursive(k, s, len-1) + [s.disk.sectors[DiskLogAddr(len-1)]]
}

// Interpret the disk as a Datum log
function DiskLog(k:Constants, s:Variables) : seq<Datum>
    requires DiskLogPlausible(k, s);
{
    var super := Disk.PeekF(k.disk, s.disk, 0);
    DiskLogRecursive(k, s, super.value)
}

// Interpret the persistent system state (disk) as a map
function IPersistent(k:Constants, s:Variables) : imap<int, int>
    requires Inv(k, s)
{
    ILog(DiskLog(k, s))
}

// Refinement to an AbstractMap
function I(k:Constants, s:Variables) : AbstractMap.Variables
    requires Inv(k, s);
{
    AbstractMap.Variables(IEphemeral(k, s), IPersistent(k, s))
}

function Ik(k:Constants) : AbstractMap.Constants
{
    AbstractMap.Constants()
}

lemma InvImpliesRefinementInit(k:Constants, s:Variables)
    requires Init(k, s);
    ensures AbstractMap.Init(Ik(k), I(k, s));
{
    reveal_ILog();
    reveal_ILogKey();
    assert IEphemeral(k, s) == AbstractMap.EmptyMap();  // OBSERVE
    reveal_DiskLogRecursive();
} 

lemma InvImpliesRefinementNext(k:Constants, s:Variables, s':Variables)
    requires Next(k, s, s');
    requires Inv(k, s);
    ensures AbstractMap.Next(Ik(k), I(k, s), I(k, s'));
{
} 


} // module RefinementProof
