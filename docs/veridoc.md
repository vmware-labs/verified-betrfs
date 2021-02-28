# Trusted crash-safe dictionary spec

**MapSpec/UI.s.dfy** Defines the "UI Op", used as labels on transitions of many of our
state machines. These labels correspond to the user-visible behavior
of the state machine. So for example: implementation handlers (Main.s.dfy)
connect their inputs and outputs to the UI ops of the transitions they perform,
and state machine refinements preserve UI ops. This is how we connect the
behavior of our main handlers with the behavior of the MapSpec.

**MapSpec/UIStateMachine.s.dfy** Abstract module for state machines with transitions labeled by UIOps.
Provides a little bit of convenience for abstracting things over
state machines.

**MapSpec/MapSpec.s.dfy** Basic dictionary state machine.

**MapSpec/ThreeStateVersioned.s.dfy** Our definition of crash-safety.


**MapSpec/ThreeStateVersionedMap.s.dfy** 

# Environment spec

**ByteBlockCacheSystem/AsyncDiskModel.s.dfy** An async disk allows concurrent outstanding I/Os. The disk is a sequence of bytes.

(Real disks constrain I/Os to fall on logical-block-address boundaries, but we're
ignoring that constraint for now.)


# Implementation spec

**Impl/MainDiskIOHandler.s.dfy** DiskInterface

**Impl/Main.s.dfy** Contains the abstract 'Main' module, which an implementation
must refine, that is, it must define the global state type,
implement the handle methods, and meet all of the contracts
demanded by this file. (See MainHandlers.i.dfy)

# Abstract B-epsilon tree

**Betree/Graph.i.dfy** An abstract graph that tracks dependencies.
It is an interface implemented by BetreeGraph (and the refined
PivotBetreeGraph): trees whose dependencies are child pointers that
reference other nodes.
It is used by the BlockInterface to identify which blocks can be
garbage-collected because they're unreachable from the graph roots.


**Betree/Transactable.i.dfy** A Transactable is a state machine defined by atomically gluing together
groups of a few step primitives. Each BetreeSpec operation performs
an atomic sequence of cache updates, such as a block allocation
followed by a write (which includes a reference to the allocated block).

Note that these aren't disk transactions; we're not assuming anything
atomic about the I/O subsystem. Transactable is a way of defining a
complex in-memory atomic action by composing simpler primitives offered
by an underlying module (the cache). This is (metatheoretically) safe with
respect to crashes, because the effect of a crash (to reset the RAM) can't
distinguish whether that reset occurs within or after a transaction.
It's not safe with respect to CPU concurrency, which is okay because
we don't yet expliot it.

**Betree/BlockInterface.i.dfy** A BlockInterface lets its client code (the Betree) perform atomic sequences
of block allocation (assigning a new value),
block write (replacing an existing value),
and read steps.
It also supports a GC step that frees some subset of unreferenced blocks.


**Betree/BetreeSpec.i.dfy** Defines the basic B-e-tree-shaped operations.

* A Query is satisfied by examining enough of the tree to observe a
terminating message list.
* Insert shoves a single message into the root.
* Flush moves a bundle of messages from a node to one of its children.
* Grow inserts a new layer at the top of the tree to admit growth.
* Redirect replaces a subtree with a semantically-equivalent one.
'Merge' and 'Split' are both special cases.


**Betree/Betree.i.dfy** Betree lowers the "lifted" op-sequences of BetreeSpec down to concrete state machine
steps that advance the BetreeBlockInterface as required by BetreeSpec.
It also interleaves Betree operations with BlockInterface garbage collection.

TODO(jonh): This probably should get renamed; its place in the heirarchy
is confusing.


**Betree/BetreeInv.i.dfy** Invariants about Betrees: lookup structure, non-equivocation, and
preservation.
TODO(jonh) and apparently a bunch of dead code! See TODO inline.


**Betree/Betree_Refines_Map.i.dfy** Refinement proof from Betree to Map.


# Pivot B-epsilon tree

**PivotBetree/Bounds.i.dfy** Defines bounds on various abstract quantities, such as the number
of children of a node.


**PivotBetree/PivotBetreeGraph.i.dfy** 

**PivotBetree/PivotBetreeBlockInterface.i.dfy** 

**PivotBetree/PivotBetreeSpec.i.dfy** A PivotBetree refines a Betree, carrying forward the tree structure
but refining the abstract infinite key maps with key ranges separated
by pivot keys.


**PivotBetree/PivotBetreeSpecWFNodes.i.dfy** 

**PivotBetree/PivotBetreeSpecRefinement.i.dfy** Lays out the abstraction function between the datatypes, setting
up for PivotBetree_Refines_Betree.


**PivotBetree/PivotBetree.i.dfy** Like Betree, PivetBetree lowers the "lifted" op-sequences of PivotBetreeSpec
down to concrete state machine steps that advance the PivotBetreeBlockInterface
as required by BetreeSpec. The only difference is that the interface has a more
concrete (pivot-y) type.


**PivotBetree/PivotBetree_Refines_Betree.i.dfy** Refinement from PivotBetree for Betree.
Note that this file just exposes the interpretation
functions and lemmas.

The meat of the logic is in PivotBetree
and PivotBetreeSpecRefinement.


**PivotBetree/StatesViewPivotBetree.i.dfy** 

**PivotBetree/PivotBetree_Refines_Map.i.dfy** Composes the two refinements:

PivotBetree -> Betree
Betree -> Map

To yield

PivotBetree -> Map


**PivotBetree/StatesViewPivotBetree_Refines_StatesViewMap.i.dfy** Lifts the refinement:

PivotBetree -> Map

to

StatesView PivotBetree -> StatesView Map

via the StatesView functor


# BlockCache

**BlockCacheSystem/AsyncSectorDiskModelTypes.i.dfy** 

**BlockCacheSystem/DiskLayout.i.dfy** 

**BlockCacheSystem/JournalRange.i.dfy** 

**BlockCacheSystem/JournalInterval.i.dfy** 

**BlockCacheSystem/SectorType.i.dfy** 

**BlockCacheSystem/BlockDisk.i.dfy** An AsyncSectorDiskModel allows concurrent outstanding I/Os to a disk where each "sector"
is some higher-level Node datatype. A later refinement step shows how to marshall and align
these Nodes to the byte-ranges of the (trusted) AsyncDiskModel.


**BlockCacheSystem/JournalDisk.i.dfy** 

**BlockCacheSystem/BlockCache.i.dfy** A BlockCache implements the BlockInterface by caching over an
BlockDisk. At this layer, the disk provides high-level sectors
(containing either this module's indirection tables or the Node
type of the application, a not-yet-bound parameter).

The BlockCache provides Persistent, Frozen, and Ephemeral views of the
application data, facilitating the crash-safety and crash recovery behavior.


**BlockCacheSystem/BlockJournalDisk.i.dfy** 

**BlockCacheSystem/JournalCache.i.dfy** 

**BlockCacheSystem/BetreeCache.i.dfy** Bind a Betree to a BlockCache to get the behavior of both: the map implementation of a Betree,
and the crash-safety implementation of a BlockCache.


**BlockCacheSystem/BlockSystem.i.dfy** Attach a BlockCache to a Disk


**BlockCacheSystem/JournalSystem.i.dfy** Attach a BlockCache to a Disk


**BlockCacheSystem/BlockJournalCache.i.dfy** 

**BlockCacheSystem/BlockSystem_Refines_StatesView.i.dfy** 

**BlockCacheSystem/JournalSystem_Refines_JournalView.i.dfy** 

**BlockCacheSystem/BetreeSystem.i.dfy** Instantiate the {PivotBetree, BlockCache} code in a System (model of the environment).
("Bottom lettuce")

TODO(jonh): Rename PivotBetreeBlockCacheSystem. [approved by thance]

**BlockCacheSystem/BetreeSystem_Refines_StatesViewPivotBetree.i.dfy** Take the whole crash-safe BlockCacheSystem, and constrain it to
run the (Pivot)Betree as its client, thereby yielding a 3-state-crash-safe
Betree. (We'll eventually tie that up the stack to get a 3-state-crash-safe
map.)


**BlockCacheSystem/BetreeSystem_Refines_StatesViewMap.i.dfy** Composes the two refinements:

BetreeSystem -> StatesView PivotBetree
StatesView PivotBetree -> StatesView Map

To yield

BetreeSystem -> StatesView Map


**BlockCacheSystem/BetreeJournalSystem.i.dfy** 

**BlockCacheSystem/BetreeJournalSystem_Refines_CompositeView.i.dfy** 

**BlockCacheSystem/BetreeJournalSystem_Refines_ThreeStateVersionedMap.i.dfy** Composes the two refinements:

BetreeJournalSystem -> CompositeView
CompositeView -> ThreeStateVersioned Map

To yield

BetreeJournalSystem -> ThreeStateVersioned Map


# ByteCache

**ByteBlockCacheSystem/JournalBytes.i.dfy** 

**ByteBlockCacheSystem/Marshalling.i.dfy** Defines the interpretation of a sector of bytes as
an abstract PivotBetree Node or a BlockCache IndirectionTable


**ByteBlockCacheSystem/InterpretationDiskOps.i.dfy** 

**ByteBlockCacheSystem/ByteCache.i.dfy** Wraps a BetreeBlockCache (which does I/O in high-level Node sectors) into
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


**ByteBlockCacheSystem/InterpretationDiskContents.i.dfy** 

**ByteBlockCacheSystem/InterpretationDisk.i.dfy** 

**ByteBlockCacheSystem/ByteSystem.i.dfy** 

**ByteBlockCacheSystem/ByteSystem_Refines_BetreeJournalSystem.i.dfy** 

**ByteBlockCacheSystem/ByteSystem_Refines_ThreeStateVersionedMap.i.dfy** Composes the two refinements:

ByteSystem -> BetreeJournalSystem
BetreeJournalSystem -> ThreeStateVersioned Map

To yield

ByteSystem -> ThreeStateVersioned Map


# Implementation

**Impl/BlockAllocatorModel.i.dfy** A BlockAllocator tracks which blocks are allocated, to safely allocate
blocks unused by any view.


**Impl/BucketGeneratorModel.i.dfy** A mathematical description of bucket generators.
It's like an iterator, but it doesn't directly refer to an actual bucket.
The bucket may be implicit.


**Impl/DiskOpModel.i.dfy** 

**Impl/IndirectionTable.i.dfy** The heap-y implementation of IndirectionTableModel.


**Impl/JournalistMarshallingModel.i.dfy** 

**Impl/JournalistParsingImpl.i.dfy** 

**Impl/MkfsModel.i.dfy** 

**Impl/NodeImpl.i.dfy** Implements PivotBetree/PivotBetreeSpec.Node. (There's no Model file
because Node is already a precise functional model of this code.)


**Impl/AllocationReport.i.dfy** 

**Impl/BlockAllocatorImpl.i.dfy** A BlockAllocator tracks which blocks are allocated, to safely allocate
blocks unused by any view.


**Impl/BucketGeneratorImpl.i.dfy** 

**Impl/BucketSuccessorLoopModel.i.dfy** 

**Impl/DiskOpImpl.i.dfy** TODO a better name might be IOImpl, but that's already
taken. TODO rename that other thing, then rename this.

**Impl/JournalistMarshallingImpl.i.dfy** 

**Impl/StateSectorModel.i.dfy** 

**Impl/BucketSuccessorLoopImpl.i.dfy** 

**Impl/JournalistImpl.i.dfy** 

**Impl/MarshallingModel.i.dfy** Parses bytes and returns the data structure (a Pivot-Node Sector) used by
the Model.

Annoyingly, our marshaling framework doesn't enforce bijectivity.
So we talk only about parsing, and define marshal(X) as anything
that produces an output that parses to X.

TODO(jonh): rename to ModelParsing.


**Impl/StateBCModel.i.dfy** 

**Impl/StateSectorImpl.i.dfy** 

**Impl/IOModel.i.dfy** IO functions used by various StateModel verbs.
Updates data structures as defined in StateModel.
Interacts with the disk via StateModel.IO, which abstracts
MainDiskIOHandlers.s.dfy.

Also, the code that reads in indirection tables and nodes.


**Impl/BookkeepingModel.i.dfy** 

**Impl/DeallocModel.i.dfy** 

**Impl/FlushModel.i.dfy** 

**Impl/GrowModel.i.dfy** 

**Impl/LeafModel.i.dfy** 

**Impl/SplitModel.i.dfy** 

**Impl/SuccModel.i.dfy** See dependency graph in MainHandlers.dfy

**Impl/SyncModel.i.dfy** See dependency graph in MainHandlers.dfy

**Impl/EvictModel.i.dfy** 

**Impl/FlushPolicyModel.i.dfy** 

**Impl/CacheImpl.i.dfy** Implements map<Reference, Node>

TODO(thance): We need a CacheModel, because this is taking too big a leap
from map<Reference, Node>.


**Impl/InsertModel.i.dfy** 

**Impl/MarshallingImpl.i.dfy** 

**Impl/StateBCImpl.i.dfy** 

**Impl/IOImpl.i.dfy** 

**Impl/Mkfs.i.dfy** 

**Impl/BookkeepingImpl.i.dfy** 

**Impl/CommitterImpl.i.dfy** 

**Impl/DeallocImpl.i.dfy** 

**Impl/FlushImpl.i.dfy** 

**Impl/GrowImpl.i.dfy** 

**Impl/LeafImpl.i.dfy** 

**Impl/SplitImpl.i.dfy** 

**Impl/StateModel.i.dfy** This file represents immutability's last stand.
It is the highest-fidelity representation of the implementation
that can be represented with immutable datatypes.

For example, it has a model of the root bucket which does not exist in
BlockCache.  It also represents indirection table as a map to pairs, rather
than two maps, because real, mutable implementation uses a map to pairs.


**Impl/FullImpl.i.dfy** 

**Impl/HandleReadResponseModel.i.dfy** 

**Impl/HandleWriteResponseModel.i.dfy** 

**Impl/QueryModel.i.dfy** See dependency graph in MainHandlers.dfy

**Impl/SyncImpl.i.dfy** See dependency graph in MainHandlers.dfy

**Impl/CoordinationModel.i.dfy** 

**Impl/EvictImpl.i.dfy** 

**Impl/HandleReadResponseImpl.i.dfy** 

**Impl/HandleWriteResponseImpl.i.dfy** 

**Impl/SuccImpl.i.dfy** See dependency graph in MainHandlers.dfy

**Impl/FlushPolicyImpl.i.dfy** 

**Impl/QueryImpl.i.dfy** See dependency graph in MainHandlers.dfy

**Impl/InsertImpl.i.dfy** See dependency graph in MainHandlers.dfy

**Impl/CoordinationImpl.i.dfy** 

**Impl/MainHandlers.i.dfy** Implements the application-API-handler obligations laid out by Main.s.dfy. TODO rename in a way that emphasizes that this is a module-refinement of the abstract Main that satisfies its obligations.


# Verified crash-safe refinements

**MapSpec/Journal.i.dfy** 

**MapSpec/TSJ.i.dfy** TSJ = Three-State-Journaled.
There are three states, and each one has a journal.
We also track two extra journals ("gamma" and "delta")
which describe the relationships between the three
states.

**MapSpec/TSJMap.i.dfy** 

**MapSpec/TSJMap_Refines_ThreeStateVersionedMap.i.dfy** 

# Verified crash-safe refinements

**Versions/VOp.i.dfy** Labels for transitions of the JournalView and StatesView.
This allows us to tie their behaviors together. Unfortunately,
it's a little clunky.

**Versions/JournalView.i.dfy** Abstraction of the journal side of the system.

**Versions/StatesView.i.dfy** Abstraction of the cache/betree side of the system.

**Versions/StatesViewMap.i.dfy** 

**Versions/CompositeView.i.dfy** Combine StatesView and JournalView.

**Versions/CompositeView_Refines_TSJMap.i.dfy** 

**Versions/CompositeView_Refines_ThreeStateVersionedMap.i.dfy** Composes the two refinements:

CompositeView -> TSJMap
TSJMap -> ThreeStateVersioned Map

To yield

CompositeView -> ThreeStateVersioned Map


# Trusted libraries

**lib/Base/MapRemove.s.dfy** Defines a MapRemove1 operation for removing a key from a
the built-in map<K,V> type, and declares a trusted, compilable
version.

TODO On principle, it'd be nice to remove our dependence
on compiling the built-in map<K, V> entirely, and just
replace them with our own hash tables. There are only
a few minor usages left.

**lib/Base/MathAxioms.s.dfy** This files contains math axioms which seem to be missing
from Dafny's (Boogie's?) math reasoning, resulting in
an incomplete theory.
TODO follow up on these: file a ticket with Dafny about
shoring up these holes.

**lib/Base/NativeBenchmarking.s.dfy** Some utilities for benchmarking via explicit instrumentation.

**lib/Base/Option.s.dfy** 

**lib/Base/KeyType.s.dfy** 

# Verified libraries

**lib/Base/SetBijectivity.i.dfy** 

**lib/Base/Sets.i.dfy** 

**lib/Base/mathematics.i.dfy** 

**lib/Base/BitsetLemmas.i.dfy** Some support math to support Bitmap module.


**lib/Base/DebugAccumulator.i.dfy** Used for counting up instances of objects, while debugging some
memory leaks in the GC implementation. (Looking forward to Rust
& explicit memory management.)

**lib/Base/LinearOption.i.dfy** 

**lib/Base/Maps.i.dfy** TODO(rob): Split into Maps and IMaps

**lib/Base/PackedIntsLib.i.dfy** 

**lib/Base/sequences.i.dfy** 

**lib/Base/Arrays.i.dfy** 

**lib/Base/Message.i.dfy** The messages propagated down a B-epsilon tree. Each message either
completely defines the value of the key, or is a delta that modifies the
value defined by prior messages.

Delta forms a monoid with a monoid-action on the values
(https://en.wikipedia.org/wiki/Monoid_action)

**lib/Base/Multisets.i.dfy** 

**lib/Base/total_order.i.dfy** 

**lib/Base/total_order_impl.i.dfy** Methods for total_orders go here because we don't want
Integer_Order to have any methods, since we don't want to require
backends to support compiling ints.

# Bucket implementation

**lib/Buckets/BoundedPivotsLib.i.dfy** Provides definitions and libraries for pivot tables. A pivot
table is a sorted list of *pivot* keys that divides the keyspace into
contiguous ranges.


**lib/Buckets/MapSeqs.i.dfy** Utilities for converting from a (seq of keys, seq of values) representation
and a map<key, value> representation.

Currently specialized to keys and messages, could be made more general.

seqs -> map representation is lossy, unless the input keys are sorted.
map -> seqs representation is invertible.


**lib/Buckets/PackedStringArray.i.dfy** 

**lib/Buckets/BucketMap.i.dfy** 

**lib/Buckets/PackedStringArrayMarshalling.i.dfy** 

**lib/Buckets/BucketsLib.i.dfy** A Bucket is two sequences: a sequence of keys and
a sequence of messages. The interpretation of a bucket
is a map, given by to_map().

Buckets generally should have keys in sorted order.
However, most operations are defined so as it make sense
without that requirement, thus the implementation can
avoid costly sortedness checks.

The on-disk representation and the most common in-memory
representation of a bucket is as 2 sequences (PackedKV)
so this is the most straightforward representation of such
a thing.


**lib/Buckets/BucketIteratorModel.i.dfy** A mathematical description of bucket iterators.
The implementation is defined in BucketImpl together with MutBucket.


**lib/Buckets/BucketWeights.i.dfy** Assigning weights to buckets guides the flushing algorithm to decide
which child to push messages towards. TODO(thance): help!

TODO(jonh&robj) Proposed restructuring: Weights don't belong at the
BucketsLib layer.  They belong at the concrete representation
layer, where the byte encoding is known.  The only reason they are
at this layer is that we use a function definition of flushing,
which means we have to deterministically know which flush we are
going to do.  If we use a predicate definition instead, then we can
describe the non-deterministic universe of valid flushes and
concretize at a lower layer.

**lib/Buckets/BucketFlushModel.i.dfy** TODO rename this file to be BucketFlushing or something

**lib/Buckets/PackedKV.i.dfy** 

**lib/Buckets/LKMBPKVOps.i.dfy** 

**lib/Buckets/PackedKVMarshalling.i.dfy** 

**lib/Buckets/BucketImpl.i.dfy** Collects singleton message insertions efficiently, avoiding repeated
replacement of the immutable root Node. Once this bucket is full,
it is flushed into the root in a batch.
This module implements PivotBetreeSpec.Bucket (the model for class
MutBucket).
The MutBucket class also supplies Iterators using the functional
Iterator datatype from BucketIteratorModel, which is why there is no
BucketIteratorImpl module/class.

# Data structure library

**lib/DataStructures/BitmapModel.i.dfy** Maintains a compact set of integers using a packed-uint64 bitmap
representation.


**lib/DataStructures/BtreeModel.i.dfy** 

**lib/DataStructures/LinearDList.i.dfy** 

**lib/DataStructures/LinearMutableMapBase.i.dfy** 

**lib/DataStructures/LruModel.i.dfy** An LRU-queue.


**lib/DataStructures/BitmapImpl.i.dfy** Maintains a compact set of integers using a packed-uint64 bitmap
representation.


**lib/DataStructures/LinearContentMutableMap.i.dfy** 

**lib/DataStructures/LinearMutableMap.i.dfy** 

**lib/DataStructures/MutableBtree.i.dfy** 

**lib/DataStructures/KMBtree.i.dfy** 

**lib/DataStructures/LinearLru.i.dfy** 

**lib/DataStructures/LinearUSeq.i.dfy** 

# Language utilities

**lib/Lang/Inout.i.dfy** 

**lib/Lang/LinearBox.s.dfy** 

**lib/Lang/LinearMaybe.s.dfy** 

**lib/Lang/NativeTypes.s.dfy** 

**lib/Lang/LinearBox.i.dfy** 

**lib/Lang/LinearSequence.s.dfy** 

**lib/Lang/System/Arithmetic.s.dfy** unsigned integer addition with overflow allowed

**lib/Lang/System/Bits.s.dfy** Provides access to hardware functions for bit manipulation,
including 128-bit registers.

**lib/Lang/System/PackedInts.s.dfy** Language augmentation providing access to byte-level integer casting.

**lib/Lang/System/SeqComparison.s.dfy** Trusted access to memcmp

**lib/Lang/LinearSequence.i.dfy** 

**lib/Lang/System/F2_X.s.dfy** Provides access to hardware functions for mod 2 polynomial
multiplication and division.

**lib/Lang/System/NativeArrays.s.dfy** Language augmentation with faster array methods.

# Marshalling library

**lib/Marshalling/Maps.i.dfy** 

**lib/Marshalling/Math.i.dfy** Based on IronFleet's math library.
I pulled out only the functions we need for the marshalling code,
and in a few cases rewrote the proof from scratch to avoid pulling in
a lot of dependencies.

**lib/Marshalling/Seqs.i.dfy** 

**lib/Marshalling/Util.i.dfy** 

**lib/Marshalling/GenericMarshalling.i.dfy** Main marshalling library for marshalling generic datatypes
out of tuples, arrays, unions, bytes, uint32, and uint64.

# Math library

From IronFleet, but mostly unused in VeriBetrKV

**lib/Math/bases.i.dfy** 

# CRC32-C Specification

**lib/Checksums/CRC32C.s.dfy** Our disk model relies on assumptions relating to our checksum
algorithm, CRC-32 (namely that a block with a valid checksum cannot
become corrupted to another block with a valid checksum).
Thus, we need the CRC-32 algorithm in our TCB. The validity of our
disk model is dependent upon its mathematical properties.

Here, CRC32-C is defined mathematically, in terms of the remainder
of polynomial division, where bit strings are interpreted as polynomials
over F_2.

# CRC32-C Implementation

**lib/Checksums/Nonlinear.i.dfy** This file is meant to be run with nonlinear-arithmetic enabled in z3.
It only exports really basic lemmas (commutativity, associativity, etc.)
so that these facts can be used by files that use /noNLarith

**lib/Checksums/CRC32C_PowDef.i.dfy** 

**lib/Checksums/F2_X_Lemmas.i.dfy** 

**lib/Checksums/MathLemmas.i.dfy** More complicated math lemmas. This file is meant to be run with `/noNLarith`.
Call into NonlinearLemmas for basic nonlinear facts rather than relying on Z3.
TODO combine with other math lib?

**lib/Checksums/BitLemmas.i.dfy** 

**lib/Checksums/CRC32C_Lemmas.i.dfy** 

**lib/Checksums/CRC32C_Lut.i.dfy** 

**lib/Checksums/CRC32CArrayImpl.i.dfy** Yeah this is basically a copy of CRC32_C_Impl but with seq replaced by array.
TODO if we use (linear) sequences everywhere instead of arrays we can remove this.

**lib/Checksums/CRC32CImpl.i.dfy** Implementation of CRC32-C, using the
using the _mm_crc32_u64 intrinsic, pipelined and proven
correct using fancy polynomial math.

See https://github.com/komrad36/CRC for a more detailed explanation.

