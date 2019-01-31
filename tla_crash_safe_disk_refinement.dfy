include "abstract_map.dfy"
include "tla_crash_safe_disk.dfy"

module RefinementProof {
import opened AppTypes
import opened LogImpl
import AbstractMap

// Interpret a log sequence of Datums as a map
function {:opaque} ILog(log:seq<Datum>) : imap<int, int>
{
    imap k | AbstractMap.InDomain(k) :: EvalLog(log, k)
}

function {:opaque} DiskLogRecursive(k:Disk.Constants, s:Disk.Variables, len:nat) : seq<Datum>
    requires len+1 <= k.size
    requires Disk.WF(k, s)
{
    if len==0 
    then []
    else DiskLogRecursive(k, s, len-1) + [s.sectors[DiskLogAddr(len-1)]]
}

// Interpret the disk as a Datum log
function DiskLog(k:Disk.Constants, s:Disk.Variables) : seq<Datum>
    requires DiskLogPlausible(k, s)
{
    var super := Disk.PeekF(k, s, 0);
    DiskLogRecursive(k, s, super.value)
}

lemma HowToMakeADiskLog(k:Disk.Constants, s:Disk.Variables, log:seq<Datum>)
    requires DiskLogPlausible(k, s)
    requires |log| <= Disk.PeekF(k, s, 0).value
    requires forall i :: 0<=i<|log| ==> log[i] == Disk.PeekF(k, s, DiskLogAddr(i))
    ensures DiskLogRecursive(k, s, |log|) == log
{
    reveal_DiskLogRecursive();
    if log != [] {
        HowToMakeADiskLog(k, s, log[..|log|-1]);
    }
}

// Interpret the persistent system state (disk) as a map
function IPersistent(k:Constants, s:Variables) : imap<int, int>
    requires Inv(k, s)
{
    ILog(DiskLog(k.disk, s.disk))
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
    requires Inv(k, s)
{
    AbstractMap.Variables(IEphemeral(k, s), IPersistent(k, s))
}

function Ik(k:Constants) : AbstractMap.Constants
{
    AbstractMap.Constants()
}

lemma InvImpliesRefinementInit(k:Constants, s:Variables)
    requires Init(k, s)
    ensures AbstractMap.Init(Ik(k), I(k, s))
{
    reveal_ILog();
    reveal_FindIndexInLog();
    assert IEphemeral(k, s) == AbstractMap.EmptyMap();  // OBSERVE
    reveal_DiskLogRecursive();
} 

lemma InvImpliesWF(k:Constants, s:Variables)
    requires Inv(k, s)
    ensures AbstractMap.WF(I(k, s))
{
    reveal_ILog();
    reveal_FindIndexInLog();
}

lemma InvImpliesRefinementNext(k:Constants, s:Variables, s':Variables)
    requires Next(k, s, s')
    requires Inv(k, s)
    ensures AbstractMap.WF(I(k, s))
    ensures AbstractMap.WF(I(k, s'))
    ensures AbstractMap.Next(Ik(k), I(k, s), I(k, s'))
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
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.SpontaneousCrash);
        }
        case ReadSuperblock => {
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Stutter());
        }
        case ScanDiskLog => {
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Stutter());
        }
        case TerminateScan => {
            HowToMakeADiskLog(k.disk, s.disk, s.memlog);
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Stutter());
        }
        case Append(datum) => {
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Write(datum));
        }
        case Query(datum) => {
            calc {
                datum.value;
                EvalLog(s.memlog, datum.key).value;
                IEphemeral(k, s)[datum.key];
            }
            assert Is' == Is;
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
