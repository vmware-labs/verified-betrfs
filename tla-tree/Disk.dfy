module Disk {

type Sector(!new,==)

type LBA = int
datatype Constants = Constants(size:LBA)
datatype Variables = Variables(sectors:seq<Sector>)

predicate ValidLBA(k:Constants, lba:LBA)
{
    0 <= lba < k.size
}

predicate WF(k:Constants, s:Variables)
{
    // All valid lbas are present in the sectors sequence.
    |s.sectors| == k.size
}

predicate Init(k:Constants, s:Variables)
{
    && WF(k, s)
}

predicate Peek(k:Constants, s:Variables, lba:LBA, sector:Sector)
{
    && WF(k, s)
    && ValidLBA(k, lba)
    && s.sectors[lba] == sector
}

function PeekF(k:Constants, s:Variables, lba:LBA) : Sector
    requires WF(k, s)
    requires ValidLBA(k, lba)
{
    s.sectors[lba]
}

predicate Read(k:Constants, s:Variables, s':Variables, lba:LBA, sector:Sector)
{
    && Peek(k, s, lba, sector)
    && s' == s
}

predicate Write(k:Constants, s:Variables, s':Variables, lba:LBA, sector:Sector)
{
    && WF(k, s)
    && ValidLBA(k, lba)
    && s'.sectors == s.sectors[lba := sector]
}

predicate Idle(k:Constants, s:Variables, s':Variables)
{
    && s' == s
}

datatype Step =
    | ReadStep(lba:LBA, sector:Sector)
    | WriteStep(lba:LBA, sector:Sector)
    | IdleStep

predicate NextStep(k:Constants, s:Variables, s':Variables, step:Step)
{
    match step {
        case ReadStep(lba, sector) => Read(k, s, s', lba, sector)
        case WriteStep(lba, sector) => Write(k, s, s', lba, sector)
        case IdleStep => Idle(k, s, s')
    }
}

} // module Disk
