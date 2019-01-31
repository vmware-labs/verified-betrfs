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
datatype Variables = Variables(
    // Actual disk state. We get to keep only this state across a crash.
    disk:Disk.Variables,
    // Operating mode, so we can keep track of a recovery read.
    mode:Mode,
    // How much of the disk log is "committed": synced with the value in the log superblock.
    // Drives refinement to abstract 'persistent' state, since this is what we'll see on a recovery.
    diskCommittedSize:LBA,
    // How much of the disk log agrees with the memlog. May exceed diskCommittedSize if we've
    // done PushLogData but not yet PushLogMetadata. We need this pointer to drag the synchrony invariant
    // forward from some PushLogDatas to a PushLogMetadata that updates diskCommittedSize.
    diskPersistedSize:LBA,
    // The memory image of the log. Its prefix agrees with the disk.
    memlog:seq<Datum>)

predicate Init(k:Constants, s:Variables, diskSize:int)
{
    // By saying nothing about the other variables, they can "havoc" (take
    // on arbitrary values).
    && Disk.Init(k.disk, s.disk, diskSize)
    // Assume the disk has been mkfs'ed:
    && Disk.Peek(k.disk, s.disk, 0, Datum(0, 0))
    && s.mode.Running?
    && s.diskCommittedSize == 0
    && s.diskPersistedSize == 0
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
        && 0 <= datum.value // If disk holds a negative superblock value, we freeze.
        && s'.mode == Recover(0)
        && s'.diskCommittedSize == datum.value
        && s'.diskPersistedSize == datum.value
        && s'.memlog == []
}

// Pull blocks off the disk until we've read them all.
// Here's a PC-less event-driven thingy. Sorry.
predicate ScanDiskLog(k:Constants, s:Variables, s':Variables)
{
    exists datum ::
        && s.mode.Recover?
        && Disk.Read(k.disk, s.disk, s'.disk, DiskLogAddr(s.mode.next), datum)
        && s.mode.next + 1 < s.diskCommittedSize
        && s'.mode == Recover(s.mode.next + 1)
        && s'.diskCommittedSize == s.diskCommittedSize
        && s'.diskPersistedSize == s.diskPersistedSize
        && s'.memlog == s.memlog + [datum]
}

// We've got all the blocks. Switch to Running mode.
predicate TerminateScan(k:Constants, s:Variables, s':Variables)
{
    && s.mode.Recover?
    && Disk.Idle(k.disk, s.disk, s'.disk)
    && s.mode.next == s.diskCommittedSize   // Nothing more to read
    && s'.mode == Running
    && s'.diskCommittedSize == s.diskCommittedSize
    && s'.diskPersistedSize == s.diskPersistedSize
    && s'.memlog == s.memlog
}

// In-memory append.
predicate Append(k:Constants, s:Variables, s':Variables, datum:Datum)
{
    && s.mode.Running?
    && s'.disk == s.disk
    && s'.mode == s.mode
    && s'.diskCommittedSize == s.diskCommittedSize
    && s'.diskPersistedSize == s.diskPersistedSize
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
    && s'.diskCommittedSize == s.diskCommittedSize
    && s'.diskPersistedSize == s.diskPersistedSize
    && s'.memlog == s.memlog
    && Disk.Idle(k.disk, s.disk, s'.disk)
}

// Returns the LBA for an index in the log.
function DiskLogAddr(index:int) : LBA
{
    // +1 to skip superblock.
    index + 1
}

predicate PushLogData(k:Constants, s:Variables, s':Variables)
{
    var idx := s.diskCommittedSize;   // The log index to flush out.
    && s.mode.Running?
    && 0 <= idx < |s.memlog| // there's a non-durable suffix to write
    && Disk.Write(k.disk, s.disk, s'.disk, DiskLogAddr(idx), s.memlog[idx])
    && s'.mode == s.mode
    && s'.diskCommittedSize == s.diskCommittedSize
    && s'.diskPersistedSize == idx + 1    // Now idx is durable, too
    && s'.memlog == s.memlog
}

predicate PushLogMetadata(k:Constants, s:Variables, s':Variables)
{
    && s.mode.Running?
    && Disk.Write(k.disk, s.disk, s'.disk, 0, Datum(0, s.diskPersistedSize))
    && s'.mode == s.mode
    && s'.diskCommittedSize == s.diskPersistedSize   // drives the refinement to PersistKeys.
    && s'.diskPersistedSize == s.diskPersistedSize
    && s'.memlog == s.memlog
}

// This promise is br conjunct.
predicate CompleteSync(k:Constants, s:Variables, s':Variables)
{
    && s.mode.Running?
    && s.diskCommittedSize == |s.memlog|
    && s'.mode == s.mode
    && s'.diskCommittedSize == s.diskCommittedSize
    && s'.diskPersistedSize == s.diskPersistedSize
    && s'.memlog == s.memlog
    && Disk.Idle(k.disk, s.disk, s'.disk)
}

datatype Step = 
      CrashAndRecover
    | ReadSuperblock
    | ScanDiskLog
    | TerminateScan
    | Append(datum: Datum)
    | Query(datum: Datum)
    | PushLogData
    | PushLogMetadata
    | CompleteSync

predicate NextStep(k:Constants, s:Variables, s':Variables, step:Step)
{
    match step {
        case CrashAndRecover => CrashAndRecover(k, s, s')
        case ReadSuperblock => ReadSuperblock(k, s, s')
        case ScanDiskLog => ScanDiskLog(k, s, s')
        case TerminateScan => TerminateScan(k, s, s')
        case Append(datum) => Append(k, s, s', datum)
        case Query(datum) => Query(k, s, s', datum)
        case PushLogData => PushLogData(k, s, s')
        case PushLogMetadata => PushLogMetadata(k, s, s')
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
            && s.diskCommittedSize == s.disk.sectors[0].value
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
    && DiskLogPlausible(k, s)
    && LogSizeValid(k, s)
    && ScanInv(k, s)
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
//    var step :| NextStep(k, s, s', step);
//    match step {
//        case CrashAndRecover => {
////            assert LogSizeValid(k, s');
////            assert LogPrefixAgrees(k, s');
//            assert Inv(k, s');
//        }
//        case ReadSuperblock => {
////            assert LogSizeValid(k, s');
////            assert LogPrefixAgrees(k, s');
//            assert Inv(k, s');
//        }
//        case ScanDiskLog => {
////            assert LogSizeValid(k, s');
////            //assert s'.diskCommittedSize <= |s'.memlog|;
////            //assert (forall i :: 0 <= i < s'.diskCommittedSize ==> s'.disk.sectors[i+1] == s'.memlog[i]);
////            if s'.mode.Running? {
////                assert |s'.memlog| == s.mode.next + 1;
////                assert s.mode.next + 1 >= s.diskCommittedSize;
////                assert s.mode.next + 1 == s.diskCommittedSize;
////                assert s.diskCommittedSize == s'.diskCommittedSize;
////                assert s'.diskCommittedSize == s'.diskPersistedSize;
////                assert s.mode.next + 1 == s'.diskPersistedSize;
////                assert s'.diskPersistedSize <= |s'.memlog|;
////            }
////            assert LogPrefixAgrees(k, s');
//            assert Inv(k, s');
//        }
//        case TerminateScan => {
//            assert Inv(k, s');
//        }
//        case Append(datum) => {
////            assert LogSizeValid(k, s');
////            assert LogPrefixAgrees(k, s');
//            assert Inv(k, s');
//        }
//        case Query(datum) => {
////            assert LogSizeValid(k, s');
////            assert LogPrefixAgrees(k, s');
//            assert Inv(k, s');
//        }
//        case PushLogData => {
////            assert s'.diskCommittedSize == s'.disk.sectors[0].value;
////            assert LogSizeValid(k, s');
////            assert LogPrefixAgrees(k, s');
//            assert Inv(k, s');
//        }
//        case PushLogMetadata => {
////            assert LogSizeValid(k, s');
////            assert LogPrefixAgrees(k, s');
//            assert Inv(k, s');
//        }
//        case CompleteSync => {
////            assert s.diskPersistedSize <= |s.memlog|;
////            assert s'.diskCommittedSize == |s.memlog|;
////            assert s'.diskCommittedSize <= s'.diskPersistedSize;
////            assert s'.diskPersistedSize == s'.diskCommittedSize;
////            assert s'.diskPersistedSize <= |s'.memlog|;
////            assert DiskLogAddr(s'.diskCommittedSize) <= DiskLogAddr(s'.diskPersistedSize);
////            assert DiskLogAddr(s'.diskPersistedSize) <= k.disk.size;
////            assert LogSizeValid(k, s');
////            assert LogPrefixAgrees(k, s');
//            assert Inv(k, s');
//        }
//    }
}

} // module LogImpl

