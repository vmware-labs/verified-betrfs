include "abstract_map.dfy"
include "tla_crash_safe_disk.dfy"

module RefinementProof {
import opened AppTypes
import opened LogImpl
import AbstractMap

// Interpret a log sequence of Datums as a map
function {:opaque} ILog(log:seq<Datum>) : imap<int, int>
    ensures AbstractMap.completeMap(ILog(log))
{
    imap k | AbstractMap.InDomain(k) :: EvalLog(log, k).value
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
    DiskLogRecursive(k, s, DiskLogSize(k, s))
}

lemma HowToMakeADiskLog(k:Disk.Constants, s:Disk.Variables, log:seq<Datum>)
    requires DiskLogPlausible(k, s)
    requires |log| <= DiskLogSize(k, s)
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

lemma LogAppend(log:seq<Datum>, datum:Datum)
    ensures ILog(log + [datum]) == ILog(log)[datum.key := datum.value]
{
    reveal_ILog();
    reveal_FindIndexInLog();
}

lemma PushLogNoop(k:Disk.Constants, s:Disk.Variables, s':Disk.Variables, len:int)
    requires DiskLogPlausible(k, s)
    requires DiskLogPlausible(k, s')
    requires 0 <= len <= DiskLogSize(k, s)
    requires forall i :: 0<=i<len ==> s.sectors[i] == s'.sectors[i] // OBSERVE, probably
    ensures DiskLog(k, s') == DiskLog(k, s)

function {:opaque} UpdateKeySet(log:seq<Datum>) : (keys:set<int>)
    ensures forall i :: 0<=i<|log| ==> log[i].key in keys
{
    if log==[] then {} else UpdateKeySet(log[..|log|-1]) + {log[|log|-1].key}
}

lemma PushLogMetadataRefinement(k:Constants, s:Variables, s':Variables)
    requires LogImpl.PushLogMetadata(k, s, s')
    requires Inv(k, s)
    ensures AbstractMap.WF(I(k, s))
    ensures AbstractMap.WF(I(k, s'))
    ensures AbstractMap.Next(Ik(k), I(k, s), I(k, s'))
{
    var Ik := Ik(k);
    var Is := I(k, s);
    var Is' := I(k, s');
    var newIdxStart := s.diskCommittedSize;
    var newIdxEnd := s.diskPersistedSize;   // exclusive
    var logTail := s.disk.sectors[DiskLogAddr(newIdxStart) .. DiskLogAddr(newIdxEnd)];
    var keys := UpdateKeySet(logTail);
    assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.PersistKeys(keys));
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
            LogAppend(s.memlog, datum);
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Write(datum));
        }
        case Query(datum) => {
            reveal_ILog();
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Query(datum));
        }
        case PushLogData => {
            PushLogNoop(k.disk, s.disk, s'.disk, DiskLogSize(k.disk, s.disk));
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Stutter());
        }
        case PushLogMetadataStep => {
            PushLogMetadataRefinement(k, s, s');
        }
        case CompleteSync => {
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Stutter());
        }
    }
} 


} // module RefinementProof
