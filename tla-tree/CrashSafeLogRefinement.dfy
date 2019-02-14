include "CrashableMap.dfy"
include "CrashSafeLogInv.dfy"

module RefinementProof {
import opened KVTypes
import opened CrashSafeLog
import opened CrashSafeLogInv
import CrashableMap

// Interpret a log sequence of Datums as a map
function {:opaque} ILog(log:seq<Datum>) : (iv:CrashableMap.View)
    ensures CrashableMap.ViewComplete(iv)
    ensures forall k :: iv[k] == EvalLog(log, k).value;
{
    imap k | CrashableMap.InDomain(k) :: EvalLog(log, k).value
}

function {:opaque} DiskLogPrefix(k:Disk.Constants, s:Disk.Variables, len:int) : (datums:seq<Datum>)
    requires 1 <= DiskLogAddr(len) <= k.size
    requires DiskLogPlausible(k, s)
    requires DiskSectorTypeCorrect(k, s, len)
    ensures |datums| == len
    ensures forall i :: 0<=i<len ==> s.sectors[DiskLogAddr(i)] == Disk.Datablock(datums[i])
{
    if len==0
    then []
    else DiskLogPrefix(k, s, len-1) + [s.sectors[DiskLogAddr(len-1)].datum]
}

// Interpret the disk as a Datum log
function DiskLog(k:Disk.Constants, s:Disk.Variables) : seq<Datum>
    requires DiskLogPlausible(k, s)
    requires DiskSectorTypeCorrect(k, s, DiskLogSize(k, s))
{
    DiskLogPrefix(k, s, DiskLogSize(k, s))
}

// The view reflecting count operations.
function IView(k:Constants, s:Variables, count:int) : CrashableMap.View
    requires Inv(k, s)
    requires 0 <= count <= |s.memlog|
{
    ILog(s.memlog[..count])
}

function INumRunningViews(k:Constants, s:Variables) : int
    requires Inv(k, s)
{
    |s.memlog| - s.diskCommittedSize + 1
}

// Returns a sequence of views of s.memlog, from ..oldest+count-1 working backwards to ..oldest.
// The IRunningViews common case is oldest==diskCommittedSize and count==INumRunningViews,
// so the last entry is ..diskCommittedSize (the persistent view), and the first entry is
// diskCommittedSize+|s.memlog|-diskCommittedSize+1-1 == |s.memlog| -- the whole log, or the
// current ephemeral view.
function {:opaque} IViewsDef(k:Constants, s:Variables, oldest:int, count:int) : (views:seq<CrashableMap.View>)
    requires Inv(k, s)
    requires 0 <= count
    requires 0 <= oldest
    requires oldest + count <= |s.memlog| + 1
    ensures |views| == count
    ensures forall i :: 0<=i<count ==> views[i] == IView(k, s, oldest + count - i - 1)
{
    assert oldest + count - 1 <= |s.memlog|;
    if count==0 then [] else [IView(k, s, oldest + count - 1)] + IViewsDef(k, s, oldest, count-1)
}

function IRunningViews(k:Constants, s:Variables) : (views:seq<CrashableMap.View>)
    requires Inv(k, s)
    requires s.mode.Running?
{
    IViewsDef(k, s, s.diskCommittedSize, INumRunningViews(k, s))
}

// The view when we don't have a memlog
function INotRunningView(k:Constants, s:Variables) : CrashableMap.View
    requires Inv(k, s)
{
    ILog(DiskLog(k.disk, s.disk))
}

function IViews(k:Constants, s:Variables) : seq<CrashableMap.View>
    requires Inv(k, s)
{
    if s.mode.Running?
    then IRunningViews(k, s)
    else [INotRunningView(k, s)]
}

// Refinement to an CrashableMap
function Ik(k:Constants) : CrashableMap.Constants
{
    CrashableMap.Constants()
}

function I(k:Constants, s:Variables) : CrashableMap.Variables
    requires Inv(k, s)
{
    CrashableMap.Variables(IViews(k, s))
}

lemma EmptyILog()
    ensures ILog([]) == CrashableMap.EmptyMap()
    // Dafny bug: why can't I just stick this ensures on ILog defn?
{
    reveal_ILog();
}

lemma InvImpliesWF(k:Constants, s:Variables)
    requires Inv(k, s)
    ensures CrashableMap.WF(I(k, s))
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

lemma AppendRefinement(k:Constants, s:Variables, s':Variables, datum:Datum)
    requires Inv(k, s)
    requires NextStep(k, s, s', AppendStep(datum));
    ensures CrashableMap.Next(Ik(k), I(k, s), I(k, s'));
{
    var views' := IViewsDef(k, s', s'.diskCommittedSize, INumRunningViews(k, s'));
    var views := IViewsDef(k, s, s.diskCommittedSize, INumRunningViews(k, s));
    forall i | 0<=i<INumRunningViews(k, s)
        ensures views'[i+1] == views[i]
    {
        var count := s.diskCommittedSize + INumRunningViews(k, s) - i - 1;
        assert s'.memlog[..count] == s.memlog[..count]; // OBSERVE seqs
    }
    assert s'.memlog[..|s'.memlog|] == s'.memlog;   // OBSERVE seqs
    assert s.memlog[..|s.memlog|] == s.memlog;  // OBSERVE seqs
    LogAppend(s.memlog, datum);
    assert CrashableMap.NextStep(Ik(k), I(k, s), I(k, s'), CrashableMap.WriteStep(datum)); // OBSERVE witness (Step)
}

lemma InvImpliesRefinementInit(k:Constants, s:Variables)
    requires Init(k, s)
    ensures CrashableMap.Init(Ik(k), I(k, s))
{
    EmptyILog();
    assert IViews(k, s) == [CrashableMap.EmptyMap()];  // OBSERVE
} 

lemma InvImpliesRefinementNext(k:Constants, s:Variables, s':Variables)
    requires Next(k, s, s')
    requires Inv(k, s)
    ensures CrashableMap.WF(I(k, s))
    ensures CrashableMap.WF(I(k, s'))
    ensures CrashableMap.Next(Ik(k), I(k, s), I(k, s'))
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
            if (s.mode.Running?) {
                assert DiskLog(k.disk, s.disk) == s.memlog[..s.diskCommittedSize];  // OBSERVE
            }
            assert CrashableMap.NextStep(Ik, Is, Is', CrashableMap.SpontaneousCrashStep());
        }
        case ReadSuperblock => {
            assert CrashableMap.NextStep(Ik, Is, Is', CrashableMap.StutterStep);
        }
        case ScanDiskLog => {
            assert CrashableMap.NextStep(Ik, Is, Is', CrashableMap.StutterStep);
        }
        case TerminateScanStep => {
            assert s'.memlog[..s'.diskCommittedSize] == DiskLog(k.disk, s.disk); // OBSERVE
            assert IViewsDef(k, s', s'.diskCommittedSize, 1) == [INotRunningView(k, s)];    // OBSERVE
            assert CrashableMap.NextStep(Ik, Is, Is', CrashableMap.StutterStep); // OBSERVE witness (Step)
        }
        case AppendStep(datum) => {
            AppendRefinement(k, s, s', datum);
        }
        case Query(datum) => {
            assert CrashableMap.NextStep(Ik, Is, Is', CrashableMap.QueryStep(datum)); // OBSERVE
        }
        case PushLogDataStep => {
            assert IViewsDef(k, s', s'.diskCommittedSize, INumRunningViews(k, s'))
                == IViewsDef(k, s, s.diskCommittedSize, INumRunningViews(k, s)); // OBSERVE
            assert CrashableMap.NextStep(Ik, Is, Is', CrashableMap.StutterStep); // OBSERVE witness (Step)
        }
        case PushLogMetadataStep(persistentCount) => {
            var writesRetired := persistentCount - s.diskCommittedSize;
            assert CrashableMap.NextStep(Ik, Is, Is', CrashableMap.PersistWritesStep(writesRetired)); // OBSERVE witness (Step)
        }
        case CompleteSync => {
            assert CrashableMap.NextStep(Ik, Is, Is', CrashableMap.StutterStep);
        }
    }
} 


} // module RefinementProof
