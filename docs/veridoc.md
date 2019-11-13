# Trusted Libraries

**lib/Marshalling/Seqs.s.dfy** 
TODO(jonh): Not sure why this is file is .s; perhaps a holdover from
IronFleet?


**lib/NativeTypes.s.dfy** 

**lib/Option.s.dfy** 

**lib/Crypto.s.dfy** 

**lib/Maps.s.dfy** 

**lib/Marshalling/Native.s.dfy** 

**lib/sequences.s.dfy** 

**lib/total_order.s.dfy** 

# Verified Libraries

**lib/Marshalling/Maps.i.dfy** 

**lib/Marshalling/Math.i.dfy** Based on IronFleet's math library.
I pulled out only the functions we need for the marshalling code,
and in a few cases rewrote the proof from scratch to avoid pulling in
a lot of dependencies.

**lib/Math/bases.i.dfy** 

**lib/SetBijectivity.i.dfy** 

**lib/mathematics.i.dfy** 

**lib/BitsetLemmas.i.dfy** 
Some support math to support Bitmap module.


**lib/Marshalling/Seqs.i.dfy** 

**lib/Marshalling/Util.i.dfy** include "../../Common/Native/Io.s.dfy"

**lib/Sets.i.dfy** 

**lib/tttree.i.dfy** 

**lib/Bitmap.i.dfy** 
A module that maintains a compact set of integers using a packed-uint64
bitmap representation.

TODO(thance): This module has both the Model (BytemapModel) and the
Impl (class Bitmap) that implements it efficiently.


**lib/Marshalling/MarshallInt.i.dfy** include "../../../Libraries/Util/seqs_transforms.i.dfy"

**lib/MutableMapModel.i.dfy** 
Immutable (functional) model to support MutableMapImpl.  API provides an
iterator interface with a deterministic order for parsing/marshaling.
(That's why the API is/ more than just a Dafny map.)

TODO(jonh): Here and elsewhere, Model files seem to be both
API (because callers use some of the definitions as 'public' ways
to reason about the behavior of the modeled Impl) and internal
proof (the logic half of the behavior of the Impl). It would be
nice to cleanly separate these concerns.


**lib/Marshalling/GenericMarshalling.i.dfy** 

**lib/MutableMapImpl.i.dfy** 
A map implemented as a fast, mutable hash table.


**lib/LRU.i.dfy** 
An LRU-queue.


# Trusted B-epsilon Tree

**disk-betree/UI.s.dfy** 

**disk-betree/UIStateMachine.s.dfy** 

**disk-betree/MapSpec.s.dfy** 

**disk-betree/AsyncDiskModel.s.dfy** 
An async disk allows concurrent outstanding I/Os. The disk is a sequence of bytes.

(Real disks constrain I/Os to fall on logical-block-address boundaries, but we're
ignoring constraint for now.)


**disk-betree/ThreeStateVersioned.s.dfy** 
Our definition of crash-safety.


**disk-betree/MainDiskIOHandler.s.dfy** DiskInterface

**disk-betree/ThreeStateVersionedMap.s.dfy** 

**disk-betree/Main.s.dfy** 

# Verified B-epsilon Tree

**disk-betree/AsyncSectorDiskModel.i.dfy** 
An AsyncSectorDiskModel allows concurrent outstanding I/Os to a disk where each "sector"
is some higher-level Node datatype. A later refinement step shows how to marshall and align
these Nodes to the byte-ranges of the (trusted) AsyncDiskModel.

TODO disallow concurrent spatially-overlapping writes/reads

**disk-betree/Bounds.i.dfy** 
Defines bounds on various abstract quantities, such as the number
of children of a node.


**disk-betree/Graph.i.dfy** 
An abstract graph that tracks dependencies.
It is an interface implemented by BetreeGraph (and the refined
PivotBetreeGraph): trees whose dependencies are child pointers that
reference other nodes.
It is used by the BlockInterface to identify which blocks can be
garbage-collected because they're unreachable from the graph roots.


**disk-betree/Message.i.dfy** 
The messages propagated down a B-epsilon tree. Each message either
completely defines the value of the key, or is a delta that modifies the
value defined by prior messages.


**disk-betree/PivotsLib.i.dfy** 
Provides definitions and libraries for pivot tables. A pivot
table is a sorted list of *pivot* keys that divides the keyspace into
contiguous ranges.


**disk-betree/BlockAllocator.i.dfy** 
A BlockAllocator tracks which blocks are allocated, to safely allocate
blocks unused by any view.


**disk-betree/BucketsLib.i.dfy** 
A Bucket maps keys to Messages. A BucketList imparts a Message meaning
to every key obeying the Message composition rules. This module shows
how pushing messages down a tree towards a child still produces equivalent
values as viewed through the Message chain.


**disk-betree/Transactable.i.dfy** 
A Transactable is a state machine defined by atomically gluing together
groups of a few step primitives. Each BetreeSpec operation performs
an atomic sequence of cache updates, such as a block allocation
followed by a write (which includes a reference to the allocated block).


**disk-betree/BlockInterface.i.dfy** 
A BlockInterface lets its client code (the Betree) perform atomic sequences
of block allocation (assigning a new value),
block write (replacing an existing value),
and read steps.
It also supports a GC step that frees some subset of unreferenced blocks.


**disk-betree/BucketWeights.i.dfy** 
Assigning weights to buckets guides the flushing algorithm to decide
which child to push messages towards. TODO(thance): help!


**disk-betree/BetreeSpec.i.dfy** 
Defines the basic B-e-tree-shaped operations.

* A Query is satisfied by examining enough of the tree to observe a
terminating message list.
* Insert shoves a single message into the root.
(Do we still use that, now that we have a mutable write buffer at the top?)
* Flush moves a bundle of messages from a node to one of its children.
* Grow inserts a new layer at the top of the tree to admit growth.
* Redirect replaces a subtree with a semantically-equivalent one.
(when do we use that?)


**disk-betree/KVList.i.dfy** 
A list of key-message pairs, with unique, sorted keys.
TODO(robj,thance): How is it used... in MutableBucket?


**disk-betree/Betree.i.dfy** 
Betree lowers the "lifted" op-sequences of BetreeSpec down to concrete state machine
steps that advance the BetreeBlockInterface as required by BetreeSpec.
It also interleaves Betree operations with BlockInterface garbage collection.

TODO(jonh): This probably should get renamed; its place in the heirarchy
is confusing.


**disk-betree/KVListPartialFlush.i.dfy** 
I guess sometimes we want to flush only part of a node's effective KVList,
and KVList only specified full flushes?
TODO(robj,thance): Improve this doc.


**disk-betree/BetreeInv.i.dfy** 
Invariants about Betrees: lookup structure, non-equivocation, and
preservation.
TODO(jonh) and apparently a bunch of dead code! See TODO inline.


**disk-betree/MutableBucket.i.dfy** 
Collects singleton message insertions efficiently, avoiding repeated
replacement of the immutable root Node. Once this bucket is full,
it is flushed into the root in a batch.
TODO(robj): Littered with assume false!?


**disk-betree/PivotBetreeSpec.i.dfy** 
A PivotBetree refines a Betree, carrying forward the tree structure
but refining the abstract infinite key maps with key ranges separated
by pivot keys.


**disk-betree/Betree_Refines_Map.i.dfy** 
Refinement proof from Betree to Map.


**disk-betree/BlockCache.i.dfy** 
A BlockCache implements the BlockInterface by caching over an
AsyncSectorDisk. At this layer, the disk provides high-level sectors
(containing either this module's indirection tables or the Node
type of the application, a not-yet-bound parameter).

The BlockCache provides Persistent, Frozen, and Ephemeral views of the
application data, facilitating the crash-safety and crash recovery behavior.


**disk-betree/PivotBetree.i.dfy** 
Like Betree, PivetBetree lowers the "lifted" op-sequences of PivotBetreeSpec
down to concrete state machine steps that advance the PivotBetreeBlockInterface
as required by BetreeSpec. The only difference is that the interface has a more
concrete (pivot-y) type.


**disk-betree/PivotBetreeSpecRefinement.i.dfy** 
Lays out the abstraction function between the datatypes, setting
up for PivotBetree_Refines_Betree.


**disk-betree/BetreeBlockCache.i.dfy** 
Bind a Betree to a BlockCache to get the behavior of both: the map implementation of a Betree,
and the crash-safety implementation of a BlockCache.


**disk-betree/BlockCacheSystem.i.dfy** 
Attach a BlockCache to a Disk


**disk-betree/PivotBetree_Refines_Betree.i.dfy** 
"Boilerplate" for the refinement/invariant proof for PivotBetree.
Reasons about refinement between generic Ops.
Relies on logic about specific ops from PivotBetreeSpecRefinement.

This is "boilerplate" in that the difficult logic is about the Node and Op refinement
in PivotBetreeSpecRefinement; this file just "lowers" that logic from ops down to
concrete state machine steps.


**disk-betree/ThreeStateVersionedPivotBetree.i.dfy** 
Defines a 3-state instantiation PivotBetree. That is, defines what state a disk can return to
if the storage system (a PivotBetree) crashes.


**disk-betree/BlockCacheSystem_Refines_ThreeStateVersionedBlockInterface.i.dfy** 
A BlockCacheSystem -- a crash-safe block cache running a client program and
attached to our disk model -- correctly provides three-state crash safety
for the state of its program.

Ideally we would prove the refinement for an arbitrary graph, but if we
imported the abstract BlockCacheSystem and CrashSafeBlockInterface
separately then we wouldn't know they were using the same graph.  So for
now, we just prove the refinement specifically for BetreeGraph.


**disk-betree/IndirectionTableModel.i.dfy** 
An IndirectionTable maps references to locations and tracks
dependencies (accounts for locations containing references).
This module includes a reference-counting map and free list
that make discovering free blocks (and maintaining the list of
them) cheap.

TODO(thance): separate API from refcount-y implementation using
a layer of Dafny refinement.

TODO(jonh): Here "Model" means "lowest functional model of the mutable
impl". Maybe move Model to the beginning of all such usages?


**disk-betree/PivotBetree_Refines_Map.i.dfy** 
Composes the two refinements:

PivotBetree -> Betree
Betree -> Map

To yield

PivotBetree -> Map


**disk-betree/BetreeBlockCacheSystem.i.dfy** 
Instantiate the {PivotBetree, BlockCache} code in a System (model of the environment).
("Bottom lettuce")


**disk-betree/ImplModel.i.dfy** 
This file represents immutability's last stand.
It is the highest-fidelity representation of the implementation
that can be represented with immutable datatypes.

For example, it has a model of the root bucket which does not exist in
BlockCache.  It also represents indirection table as a map to pairs, rather
than two maps, because real, mutable implementation uses a map to pairs.


**disk-betree/IndirectionTableImpl.i.dfy** 
The heap-y implementation of IndirectionTableModel.


**disk-betree/BetreeBlockCacheSystem_Refines_ThreeStateVersionedPivotBetree.i.dfy** 
Take the whole crash-safe BlockCacheSystem, and constrain it to
run the (Pivot)Betree as its client, thereby yielding a 3-state-crash-safe
Betree. (We'll eventually tie that up the stack to get a 3-state-crash-safe
map.)


**disk-betree/ImplMarshallingModel.i.dfy** 
Parses bytes and returns the data structure (a Pivot-Node Sector) used by
the Model.

Annoyingly, our marshaling framework doesn't enforce bijectivity.
So we talk only about parsing, and define marshal(X) as anything
that produces an output that parses to X.

TODO(jonh): rename to ModelParsing.


**disk-betree/Marshalling.i.dfy** 
Raises ImpLMarshallingModel by converting indirection table sectors
up from IndirectionTableModel.IndirectionTable to
BlockCache.IndirectionTable (and leaving pivot node sectors alone).
(This gets used as part of the interpretation function in a refinement
proof.)

TODO(thance): This structure is convoluted. Travis has some ideas
for rearranging it. In particular, we might want to make the on-disk
representation stand alone, so that we could later prove properties
about version mutationts in the file system: that you can read old disks.


**disk-betree/ByteBetreeBlockCache.i.dfy** 
Wraps a BetreeBlockCache (which does I/O in high-level Node sectors) into
a state machine that is an AsyncDiskMachine: a client of a disk that does
I/O in bytes.

You (or past Jon) might ask: why do we refine Betree and BlockCache mostly
separately, but join them up at the Pivot level, even though we still have
a layer of refinement (pivot->byte) to go? The answer is that we never have
a "byte betree block cache" in memory; we want our program to manipulate
cooked data structures, not have to unmarshall every time we inspect a block
of bytes from the cache. We want the parsing step to be specific to the
memory->disk boundary, rather than having a refinement layer that eliminates
the Pivot Node data structure entirely.


**disk-betree/ByteBetreeBlockCacheSystem.i.dfy** 
Instantiates the ByteBetreeBlockCache program in the (trusted, byte-level)
disk model to get a System.
Proves invariants to prepare for refinement from the resulting system to the
BetreeBlockCacheSystem.

TODO(jonh): fold together/regularize ByteBetreeBlockCacheSystem_Refines_BetreeBlockCacheSystem.


**disk-betree/ImplModelIO.i.dfy** 
IO functions used by various ImplModel verbs.
Updates data structures as defined in ImplModel.
Interacts with the disk via ImplModel.IO, which abstracts
MainDiskIOHandlers.s.dfy.

Also, the code that reads in indirection tables and nodes.


**disk-betree/ByteBetreeBlockCacheSystem_Refines_BetreeBlockCacheSystem.i.dfy** 
Proves refinement from the Byte (disk-parse-y) Betree system to the Pivot-y
Betree system.  This proof is simple because all the work happens in the
invariant prep in ByteBetreeBlockCacheSystem.


**disk-betree/ImplModelCache.i.dfy** 

**disk-betree/ImplModelDealloc.i.dfy** 

**disk-betree/ImplModelFlush.i.dfy** 

**disk-betree/ImplModelGrow.i.dfy** 

**disk-betree/ImplModelLeaf.i.dfy** 

**disk-betree/ImplModelQuery.i.dfy** 

**disk-betree/ImplModelSplit.i.dfy** 

**disk-betree/ImplModelSync.i.dfy** 

**disk-betree/ImplModelEvict.i.dfy** 

**disk-betree/ImplModelFlushPolicy.i.dfy** 

**disk-betree/ImplModelInsert.i.dfy** 

**disk-betree/ImplNodes.i.dfy** 

**disk-betree/ImplState.i.dfy** 

**disk-betree/Impl.i.dfy** 

**disk-betree/ImplMarshalling.i.dfy** 

**disk-betree/ImplIO.i.dfy** 

**disk-betree/Mkfs.i.dfy** 

**disk-betree/ImplCache.i.dfy** 

**disk-betree/ImplDealloc.i.dfy** 

**disk-betree/ImplFlush.i.dfy** 

**disk-betree/ImplGrow.i.dfy** 

**disk-betree/ImplLeaf.i.dfy** 

**disk-betree/ImplSplit.i.dfy** 

**disk-betree/ImplSync.i.dfy** 

**disk-betree/ImplEvict.i.dfy** 

**disk-betree/ImplQuery.i.dfy** 

**disk-betree/ImplFlushPolicy.i.dfy** 

**disk-betree/ImplInsert.i.dfy** 

**disk-betree/MainImpl.i.dfy** 

