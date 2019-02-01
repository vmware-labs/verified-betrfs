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

function DiskLogPrefix(k:Disk.Constants, s:Disk.Variables, len:int) : seq<Datum>
    requires 1 <= DiskLogAddr(len) <= k.size
    requires DiskLogPlausible(k, s)
{
    s.sectors[1..DiskLogAddr(len)]
}

// Interpret the disk as a Datum log
function DiskLog(k:Disk.Constants, s:Disk.Variables) : seq<Datum>
    requires DiskLogPlausible(k, s)
{
    DiskLogPrefix(k, s, DiskLogSize(k, s))
}

// The view reflecting count operations.
function IView(k:Constants, s:Variables, count:int) : AbstractMap.View
    requires Inv(k, s)
{
    ILog(s.memlog[..count])
}

function INumRunningViews(k:Constants, s:Variables) : int
    requires Inv(k, s)
{
    |s.memlog| - s.diskCommittedSize + 1
}

function {:opaque} IViewsDef(k:Constants, s:Variables, start:int, count:int) : (views:seq<AbstractMap.View>)
    ensures forall i :: 0<=i<count ==> views[i] == IView(k, s, |s.memlog| - start + i)
{
    if count==0 then [] else IViewsDef(k, s, start, count-1) + [IView(k, s, |s.memlog| - start + count - 1)]
}

function IRunningViews(k:Constants, s:Variables) : (views:seq<AbstractMap.View>)
{
    IViewsDef(k, s, s.diskCommittedSize, INumRunningViews(k, s))
}

// The view when we don't have a memlog
function INotRunningView(k:Constants, s:Variables) : AbstractMap.View
    requires Inv(k, s)
{
    ILog(DiskLog(k.disk, s.disk))
}

function IViews(k:Constants, s:Variables) : seq<AbstractMap.View>
{
    if s.mode.Running?
    then IRunningViews(k, s)
    else [INotRunningView(k, s)]
}

// Refinement to an AbstractMap
function I(k:Constants, s:Variables) : AbstractMap.Variables
    requires Inv(k, s)
{
    AbstractMap.Variables(IViews(k, s))
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
//    assert IViews(k, s) == [AbstractMap.EmptyMap()];  // OBSERVE
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
    ensures forall k, i :: 0<=i<|log| && !(k in keys) ==> log[i].key != k
{
    if log==[] then {} else UpdateKeySet(log[..|log|-1]) + {log[|log|-1].key}
}

function {:opaque} IndexForKey(log:seq<Datum>, key:int) : (idx:int)
    requires key in UpdateKeySet(log)
    ensures 0<=idx<|log|
    ensures log[idx].key == key
    ensures forall j :: idx < j < |log| ==> log[j].key != key
{
    reveal_UpdateKeySet();
    if log[|log|-1].key == key
    then |log|-1
    else IndexForKey(log[..|log|-1], key)
}

lemma LogIndexFallThrough(log:seq<Datum>, logPrefix:seq<Datum>, logSuffix:seq<Datum>, k:int)
    requires log == logPrefix + logSuffix
    requires forall i :: 0<=i<|logSuffix| ==> logSuffix[i].key != k
    ensures FindIndexInLog(log, k) == FindIndexInLog(logPrefix, k)
    decreases |logSuffix|
{
    reveal_FindIndexInLog();
    if logSuffix != [] {
        var subSuffix := logSuffix[..|logSuffix|-1];
        LogIndexFallThrough(logPrefix + subSuffix, logPrefix, subSuffix, k);
        if |log| > 0 && log[|log|-1].key != k {
            assert log[..|log|-1] == logPrefix + subSuffix;    // OBSERVE (sequences)
        }
    } else {
        assert log == logPrefix;    // OBSERVE (sequences)
    }
}

// If you don't find k in the suffix of a log, you can read the prefix.
lemma LogFallThrough(log:seq<Datum>, logPrefix:seq<Datum>, logSuffix:seq<Datum>, k:int)
    requires log == logPrefix + logSuffix
    requires forall i :: 0<=i<|logSuffix| ==> logSuffix[i].key != k
    ensures ILog(log)[k] == ILog(logPrefix)[k]
{
    reveal_ILog();
    reveal_FindIndexInLog();
    LogIndexFallThrough(log, logPrefix, logSuffix, k);
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
//    assert Is'.ephemeral == Is.ephemeral;
    assert AbstractMap.WF(Is');
//    forall key
//        ensures Is'.persistent[key] == if key in keys then Is.ephemeral[key] else Is.persistent[key]
//    {
//        if key in keys {
//            var suffixIdx := IndexForKey(logTail, key);
//            var idx := newIdxStart + suffixIdx;
//            var diskLog := DiskLog(k.disk, s'.disk);
//
//            assert FindIndexInLog(diskLog, key) == Some(idx);
//
//            assert |diskLog| == s'.diskCommittedSize;
//            assert s'.diskCommittedSize == s.diskPersistedSize;
//            assert s.diskPersistedSize == |s.memlog|;
//            forall i | 0 <= i < s.diskPersistedSize
//                ensures diskLog[i] == s.memlog[i]
//            {
//                assert Disk.Peek(k.disk, s.disk, DiskLogAddr(i), s.memlog[i]);
//            }
//
//            assert diskLog == s.memlog;
//            assert FindIndexInLog(s.memlog, key) == Some(idx);
//            assert s.memlog[idx] == diskLog[idx];
//            calc {
//                IPersistent(k, s')[key];
//                ILog(DiskLog(k.disk, s'.disk))[key];
//                    { reveal_ILog(); }
//                EvalLog(diskLog, key).value;
//                EvalLog(s.memlog, key).value;
//                    { reveal_ILog(); }
//                IEphemeral(k, s)[key];
//            }
//            assert Is'.persistent[key] == Is.ephemeral[key];
//        } else {
//            var diskLog := DiskLog(k.disk, s.disk);
//            var diskLog' := DiskLog(k.disk, s'.disk);
//            var suffix := diskLog'[|diskLog|..];
//            LogFallThrough(diskLog', diskLog, suffix, key);
//            assert Is'.persistent[key] == Is.persistent[key];
//        }
//    }
//    assert AbstractMap.PersistKeys(Ik, Is, Is', keys);
//    assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.PersistKeysStep(keys));
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
            assert DiskLogPrefix(k.disk, s.disk, |s.memlog|) == s.memlog;   // OBSERVE
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
