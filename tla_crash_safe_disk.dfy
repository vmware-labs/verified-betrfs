include "abstract_map.dfy"

module Disk {
import opened AppTypes

type LBA = int
datatype Constants = Constants(size:LBA)
datatype Variables = Variables(sectors:map<LBA, Datum>)

predicate ValidLBA(k:Constants, lba:LBA)
{
    0 <= lba < k.size
}

predicate WF(k:Constants, s:Variables)
{
    // All valid lbas are present in the sectors map.
    forall i :: ValidLBA(k, i) ==> i in s.sectors.Keys
}

predicate Init(k:Constants, s:Variables, size:int)
{
    && k.size == size
    && WF(k, s)
}

predicate Peek(k:Constants, s:Variables, lba:LBA, datum:Datum)
{
    && WF(k, s)
    && ValidLBA(k, lba)
    && s.sectors[lba] == datum
}

predicate Read(k:Constants, s:Variables, s':Variables, lba:LBA, datum:Datum)
{
    && Peek(k, s, lba, datum)
    && s' == s
}

predicate Write(k:Constants, s:Variables, s':Variables, lba:LBA, datum:Datum)
{
    && WF(k, s)
    && ValidLBA(k, lba)
    && s'.sectors == s.sectors[lba := datum]
}

predicate Idle(k:Constants, s:Variables, s':Variables)
{
    && s' == s
}

} // module Disk

module LogImpl {
import opened AppTypes
import Disk
type LBA = Disk.LBA

// The "program counter" for IO steps.
datatype Mode = Reboot | Recover(next:LBA) | Running

datatype Constants = Constants(disk:Disk.Constants)
datatype Variables = Variables(disk:Disk.Variables, mode:Mode, diskLogSize:LBA, memlog:seq<Datum>)

predicate Init(k:Constants, s:Variables, diskSize:int)
{
    // By saying nothing about the other variables, they can "havoc" (take
    // on arbitrary values).
    && Disk.Init(k.disk, s.disk, diskSize)
    // Assume the disk has been mkfs'ed:
    && Disk.Peek(k.disk, s.disk, 0, Datum(0, 0))
    && s.mode.Running?
    && s.diskLogSize == 0
    && s.memlog == []
}

// This organization hides the crash operation in unchecked code, which
// is a little fishy. If I were to add '&&false' in here, the rest of 
// the spec could be totally crash-unsafe, and we'd never know. Perhaps the
// right alternative would be to have the disk belong to a higher-level
// trusted component, the way we do networks in distributed systems.
predicate CrashAndRecover(k:Constants, s:Variables, s':Variables)
{
    && s'.mode.Reboot?
    // By saying nothing about the other variables, they can "havoc" (take
    // on arbitrary values). So clearly we're not relying on memlog.
    && s'.disk == s.disk
}

// Read the superblock, which gives the size of the valid log on disk.
predicate ReadSuperblock(k:Constants, s:Variables, s':Variables)
{
    exists datum ::
        && s.mode.Reboot?
        && Disk.Read(k.disk, s.disk, s'.disk, 0, datum)
        && s'.mode == Recover(0)
        && s'.diskLogSize == datum.value
        && s'.memlog == []
}

// Pull blocks off the disk until we've read them all.
// Here's a PC-less event-driven thingy. Sorry.
predicate ScanDiskLog(k:Constants, s:Variables, s':Variables)
{
    exists datum ::
        && s.mode.Recover?
        && Disk.Read(k.disk, s.disk, s'.disk, DiskLogAddr(s.mode.next), datum)
        && (s'.mode ==
            if s.mode.next + 1 < s.diskLogSize
            then Recover(s.mode.next + 1)
            else Running)
        && s'.diskLogSize == s.diskLogSize
        && s'.memlog == s.memlog + [datum]
}

// In-memory append.
predicate Append(k:Constants, s:Variables, s':Variables, datum:Datum)
{
    && s.mode.Running?
    && s'.disk == s.disk
    && s'.mode == s.mode
    && s'.diskLogSize == s.diskLogSize
    && s'.memlog == s.memlog + [datum]
    && Disk.Idle(k.disk, s.disk, s'.disk)
}

datatype Option<T> = Some(t:T) | None

function {:opaque} FindIndexInLog(log:seq<Datum>, key:int) : (index:Option<int>)
    ensures index.Some? ==>
        && 0<=index.t<|log|
        && log[index.t].key == key
        && (forall j :: index.t < j < |log| ==> log[j].key != key)
    ensures index.None? ==> forall j :: 0 <= j < |log| ==> log[j].key != key
{
    if |log| == 0
        then None
    else if log[|log|-1].key == key
        then Some(|log|-1)
    else
        FindIndexInLog(log[..|log|-1], key)
}

function EvalLog(log:seq<Datum>, key:int) : Datum
{
    var index := FindIndexInLog(log, key);
    if index.Some?
    then log[index.t]
    else Datum(key, 0)
}

predicate Query(k:Constants, s:Variables, s':Variables, datum:Datum)
{
    && s.mode.Running?
    && datum == EvalLog(s.memlog, datum.key)
    && s'.mode == s.mode
    && s'.diskLogSize == s.diskLogSize
    && s'.memlog == s.memlog
    && Disk.Idle(k.disk, s.disk, s'.disk)
}

// Returns the LBA for an index in the log.
function DiskLogAddr(index:int) : LBA
{
    // +1 to skip superblock.
    index + 1
}

predicate WriteBack(k:Constants, s:Variables, s':Variables)
{
    var idx := s.diskLogSize;   // The log index to flush out.
    && s.mode.Running?
    && 0 <= idx < |s.memlog| // there's a non-durable suffix to write
    && Disk.Write(k.disk, s.disk, s'.disk, DiskLogAddr(idx), s.memlog[idx])
    && s'.mode == s.mode
    && s'.diskLogSize == idx + 1    // Now idx is durable, too
    && s'.memlog == s.memlog
}

// This promise is br conjunct.
predicate CompleteSync(k:Constants, s:Variables, s':Variables)
{
    && s.mode.Running?
    && s.diskLogSize == |s.memlog|
    && s'.mode == s.mode
    && s'.diskLogSize == s.diskLogSize
    && s'.memlog == s.memlog
    && Disk.Idle(k.disk, s.disk, s'.disk)
}

datatype Step = 
      CrashAndRecover()
    | ReadSuperblock()
    | ScanDiskLog()
    | Append(datum: Datum)
    | Query(datum: Datum)
    | WriteBack()
    | CompleteSync()

predicate NextStep(k:Constants, s:Variables, s':Variables, step:Step)
{
    match step {
        case CrashAndRecover => CrashAndRecover(k, s, s')
        case ReadSuperblock => ReadSuperblock(k, s, s')
        case ScanDiskLog => ScanDiskLog(k, s, s')
        case Append(datum) => Append(k, s, s', datum)
        case Query(datum) => Query(k, s, s', datum)
        case WriteBack() => WriteBack(k, s, s')
        case CompleteSync => CompleteSync(k, s, s')
    }
}

predicate Next(k:Constants, s:Variables, s':Variables)
{
    exists step:Step :: NextStep(k, s, s', step)
}

predicate DiskLogPlausible(k:Constants, s:Variables)
{
    && 1 <= k.disk.size
    && Disk.WF(k.disk, s.disk)
    && DiskLogAddr(s.disk.sectors[0].value) <= k.disk.size
}

predicate LogSizeValid(k:Constants, s:Variables)
{
    && 1 <= k.disk.size
    && Disk.WF(k.disk, s.disk)
    && (
        !s.mode.Reboot? ==>
            && s.diskLogSize == s.disk.sectors[0].value
            && DiskLogAddr(s.diskLogSize) <= k.disk.size
       )
}

predicate LogPrefixAgrees(k:Constants, s:Variables)
{
    s.mode.Running? ==>
        && s.diskLogSize <= |s.memlog|
        && LogSizeValid(k, s)
        && (forall i :: 0 <= i < s.diskLogSize ==>
            s.disk.sectors[i+1] == s.memlog[i])
}

predicate Inv(k:Constants, s:Variables)
{
    && DiskLogPlausible(k, s)
    && LogSizeValid(k, s)
    && LogPrefixAgrees(k, s)
}

lemma InvHoldsInit(size:int, k:Constants, s:Variables)
    requires 1<=size
    requires Init(k, s, size)
    ensures Inv(k, s)
{
}

lemma InvHoldsInduction(k:Constants, s:Variables, s':Variables)
    requires Inv(k, s)
    requires Next(k, s, s')
    ensures Inv(k, s')
{
    var step :| NextStep(k, s, s', step);
    match step {
        case CrashAndRecover => {
            assert LogSizeValid(k, s');
            assert LogPrefixAgrees(k, s');
        }
        case ReadSuperblock => {
            assert LogSizeValid(k, s');
            assert LogPrefixAgrees(k, s');
        }
        case ScanDiskLog => {
            assert LogSizeValid(k, s');
            assert s'.diskLogSize <= |s'.memlog|;
            assert (forall i :: 0 <= i < s'.diskLogSize ==> s'.disk.sectors[i+1] == s'.memlog[i]);
            assert LogPrefixAgrees(k, s');
        }
        case Append(datum) => {
            assert LogSizeValid(k, s');
            assert LogPrefixAgrees(k, s');
        }
        case Query(datum) => {
            assert LogSizeValid(k, s');
            assert LogPrefixAgrees(k, s');
        }
        case WriteBack => {
            assert s'.diskLogSize == s'.disk.sectors[0].value;
            assert LogSizeValid(k, s');
            assert LogPrefixAgrees(k, s');
        }
        case CompleteSync => {
            assert LogSizeValid(k, s');
            assert LogPrefixAgrees(k, s');
        }
    }
}

} // module LogImpl

