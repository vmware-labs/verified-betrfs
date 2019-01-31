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

function {:opaque} DiskLogRecursive(k:Disk.Constants, s:Disk.Variables, len:nat) : seq<Datum>
    requires len+1 <= k.size;
    requires Disk.WF(k, s);
{
    if len==0 
    then []
    else DiskLogRecursive(k, s, len-1) + [s.sectors[DiskLogAddr(len-1)]]
}

// Interpret the disk as a Datum log
function DiskLog(k:Constants, s:Variables) : seq<Datum>
    requires DiskLogPlausible(k, s);
{
    var super := Disk.PeekF(k.disk, s.disk, 0);
    DiskLogRecursive(k.disk, s.disk, super.value)
}

// Interpret the persistent system state (disk) as a map
function IPersistent(k:Constants, s:Variables) : imap<int, int>
    requires Inv(k, s)
{
    ILog(DiskLog(k, s))
}

// Interpret the ephemeral system state (memlog) as a map
function IEphemeral(k:Constants, s:Variables) : imap<int, int>
    requires Inv(k, s)
{
    if s.mode.Running?
    then ILog(s.memlog)
    else IPersistent(k, s)
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

lemma InvImpliesWF(k:Constants, s:Variables)
    requires Inv(k, s);
    ensures AbstractMap.WF(I(k, s));
{
    reveal_ILog();
    reveal_ILogKey();
}

lemma InvImpliesRefinementNext(k:Constants, s:Variables, s':Variables)
    requires Next(k, s, s');
    requires Inv(k, s);
    ensures AbstractMap.WF(I(k, s));
    ensures AbstractMap.WF(I(k, s'));
    ensures AbstractMap.Next(Ik(k), I(k, s), I(k, s'));
{
    var Ik := Ik(k);
    var Is := I(k, s);
    var Is' := I(k, s');

    InvImpliesWF(k, s);
    InvHoldsInduction(k, s, s');  // OMG line unecessary: of course Dafny is just doing this whole proof again...
    InvImpliesWF(k, s');

    var step :| NextStep(k, s, s', step);

    match step {
        case CrashAndRecover => {
//            assert !s'.mode.Running?;
//            assert Disk.Idle(k.disk, s.disk, s'.disk);
//            assert DiskLog(k, s) == DiskLog(k, s');
//            calc {
//                Is'.ephemeral;
//                IEphemeral(k, s');
//                //if s'.mode.Running? then ILog(s'.memlog) else IPersistent(k, s');
//                IPersistent(k, s');
//                IPersistent(k, s);
//                Is.persistent;
//            }
//            assert Is'.persistent == Is.persistent;
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.SpontaneousCrash);
        }
        case ReadSuperblock => {
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Stutter());
        }
        case ScanDiskLog => {
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Stutter());
        }
        case TerminateScan => {
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Stutter());
        }
        case Append(datum) => {
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Write(datum));
        }
        case Query(datum) => {
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Query(datum));
        }
        case PushLogData => {
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Stutter());
        }
        case PushLogMetadata => {
            var keys := {};
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.PersistKeys(keys));
        }
        case CompleteSync => {
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Stutter());
        }
    }
} 


} // module RefinementProof
