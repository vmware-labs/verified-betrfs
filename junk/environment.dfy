type Block = seq<char>

predicate WFBlock(block: Block) {
    |block| == 512
}

datatype Mutation = Write(address: int, data: Block) | Sync(handle: int)

datatype Disk = Disk(blocks : seq<Block>, capacity: int, inflight: seq<Mutation>)

predicate WFMutation(mutation: Mutation, disk: Disk)
{
    mutation.Write? ==> (WFBlock(mutation.data) && 0 <= mutation.address < disk.capacity)
}

predicate WFDisk(disk: Disk) {
       |disk.blocks| == disk.capacity
    && (forall block :: block in disk.blocks ==> WFBlock(block))
    && (forall write :: write in disk.writes ==> WFMutation(write, disk))
}

predicate InitDisk(disk: Disk) {
    // Manufacturer might leave arbitrary sector data lying around; user is
    // responsible to call mkfs
    true
}

predicate EnqueueMutation(disk': Disk, disk: Disk, mutation: Mutation)
    requires WFDisk(disk);
    requires WFDisk(disk');
    requires WFMutation(mutation);
{
       0 <= address < disk.capacity
    && disk'.capacity == disk.capacity
    && disk'.blocks == disk.blocks
    && disk'.inflight == disk.inflight + [mutation]
}

predicate NextWrite(disk': Disk, disk: Disk, address: int, data: Block)
    requires WFDisk(disk);
    requires WFDisk(disk');
    requires WFBlock(data);
{
    EnqueueMutation(disk', disk, Write(address, data))
}

predicate NextSync(disk': Disk, disk: Disk, handle: int)
    requires WFDisk(disk);
    requires WFDisk(disk');
{
    EnqueueMutation(disk', disk, Sync(handle))
}

predicate ReorderWrites(inflight': seq<Mutation>, inflight: seq<Mutation>) {
    exists idx :: 0 <= idx < |inflight|-1
        // can't reorder across a sync
        && inflight[idx].Write?
        && inflight[idx+1].Write?
        // can't reorder writes to the same address
        && inflight[idx].address != inflight[idx+1].address
        && inflight'[..idx] == inflight[..idx]
        && inflight'[idx] == inflight[idx+1]
        && inflight'[idx+1] == inflight[idx]
        && inflight'[idx+2] == inflight[idx+2]
}

predicate CoalesceWrite(inflight': seq<Mutation>, inflight: seq<Mutation>) {
    exists idx :: 0 <= idx < |inflight|-1
        && inflight[idx].Write?
        && inflight[idx+1].Write?
        && inflight[idx].address == inflight[idx+1].address
        // coalesce away the first write, keeping the second.
        && inflight'[..idx] == inflight[..idx]
        && inflight'[idx..] == inflight[idx+1..]
}

predicate NextReorder(disk': Disk, disk: Disk)
{
       disk'.capacity == disk.capacity
    && disk'.blocks == disk.blocks
    && (ReorderWrites(disk'.inflight, disk.inflight)
        || CoalesceWrite(disk'.inflight, disk.inflight))
}

function InflightAddressesInclude(inflight: seq<Write>, address: int)
{
    exists v :: v in inflight && v.address == address
}

function InflightValue(inflight: seq<Write>, address: int)
    requires InflightAddressesInclude(inflight, address);
{
    if inflight[0].address == address
    then
        inflight[0].value
    else
        InflightValue(inflight[1:], address)
}

predicate NextRead(disk': Disk, disk: Disk, address: int, data: Block)
    requires WFDisk(disk);
    requires WFDisk(disk');
{
       0 <= address < disk.capacity
    && data == (if InflightAddressesInclude(disk.inflight, address)
                   then InflightValue(disk.inflight, address)
                   else disk.blocks[address])
    && disk' == disk
}

predicate NextRetireSync(disk': disk, disk: Disk, handle: int)
    requires WFDisk(disk);
    requires WFDisk(disk');
{
       |disk.inflight|>0
    && disk.inflight[0].Sync?
    && disk.inflight[0].handle == handle
    && disk'.capacity == disk.capacity
    && disk'.blocks == disk.blocks
    && disk'.inflight == disk.inflight[1..]
}

predicate NextRetireWrite(disk': Disk, disk: Disk)
{
       |disk.inflight|>0
    && disk.inflight[0].Write?
    && (var write := disk.inflight[0];
           disk'.capacity == disk.capacity
        && disk'.blocks == disk.blocks[write.address := write.value]
        && disk'.inflight == disk.inflight[1..]
        )
}

// A crash of the in-memory part of the filesystem: the power went out and
// came back.
predicate NextCrash(disk': disk, disk: Disk)
    requires WFDisk(disk);
    requires WFDisk(disk');
{
       disk'.capacity == disk.capacity
    && disk'.blocks == disk.blocks
    && disk'.inflight == []
}

predicate Next(disk': Disk, disk: Disk)
    requires WFDisk(disk);
    requires WFDisk(disk');
{
       exists address, data :: NextRead(disk', disk, address, data)
    || exists address, data :: NextWrite(disk', disk, address, data)
    || exists handle :: NextSync(disk', disk, handle)
    || exists handle :: NextRetireSync(disk', disk, handle)
    || NextRetireWrite(disk', disk)
    || exists idx :: NextRetire(disk', disk, idx)
    || NextReorder(disk', disk)
    || NextCrash(disk', disk)
    || NextAdversarialCrash(disk', disk)
}

// Local Variables:
// tab-width: 4
// End:
