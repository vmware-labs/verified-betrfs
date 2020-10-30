# Trusted Libraries

**lib/Base/MapRemove.s.dfy** 

**lib/Base/MathAxioms.s.dfy** This files contains math axioms which seem to be missing
from Dafny's (Boogie's?) math reasoning, resulting in
an incomplete theory.

**lib/Base/NativeBenchmarking.s.dfy** 

**lib/Base/Option.s.dfy** 

**lib/Lang/LinearBox.s.dfy** 

**lib/Lang/LinearMaybe.s.dfy** 

**lib/Lang/NativeTypes.s.dfy** 

**lib/Base/KeyType.s.dfy** 

**lib/Lang/LinearSequence.s.dfy** 

**lib/Lang/System/Arithmetic.s.dfy** 

**lib/Lang/System/Bits.s.dfy** 

**lib/Lang/System/PackedInts.s.dfy** 

**lib/Lang/System/SeqComparison.s.dfy** 

**lib/Lang/System/F2_X.s.dfy** 

**lib/Lang/System/NativeArrays.s.dfy** 

**lib/Crypto/CRC32C.s.dfy** 

# Verified Libraries

**lib/Base/SetBijectivity.i.dfy** 

**lib/Base/Sets.i.dfy** 

**lib/Base/mathematics.i.dfy** 

**lib/Crypto/CRC32PowDef.i.dfy** 

**lib/Lang/Inout.i.dfy** 

**lib/Marshalling/Maps.i.dfy** 

**lib/Marshalling/Math.i.dfy** Based on IronFleet's math library.
I pulled out only the functions we need for the marshalling code,
and in a few cases rewrote the proof from scratch to avoid pulling in
a lot of dependencies.

**lib/Math/bases.i.dfy** 

**lib/Base/BitsetLemmas.i.dfy** 
Some support math to support Bitmap module.


**lib/Base/DebugAccumulator.i.dfy** 

**lib/Base/LinearOption.i.dfy** 

**lib/Base/Maps.i.dfy** TODO(rob): Split into Maps and IMaps

**lib/Base/PackedIntsLib.i.dfy** 

**lib/Base/sequences.i.dfy** 

**lib/Crypto/BitLemmas.i.dfy** 

**lib/Crypto/CRC32LutBitUnrolling.i.dfy** 

**lib/Crypto/CRC32LutPowers.i.dfy** 

**lib/Crypto/F2_X_Lemmas.i.dfy** 

**lib/Lang/LinearSequence.i.dfy** 

**lib/Marshalling/Seqs.i.dfy** 

**lib/Marshalling/Util.i.dfy** include "../../Common/Native/Io.s.dfy"

**lib/Base/Arrays.i.dfy** include "Marshalling/Native.s.dfy"

**lib/Base/Message.i.dfy** 

**lib/Base/Multisets.i.dfy** 

**lib/Base/total_order.i.dfy** 

**lib/Crypto/CRC32LutLemma.i.dfy** 

**lib/DataStructures/BitmapModel.i.dfy** 
Maintains a compact set of integers using a packed-uint64 bitmap
representation.


**lib/DataStructures/LinearDList.i.dfy** 

**lib/DataStructures/LinearMutableMap.i.dfy** 

**lib/DataStructures/MutableMapModel.i.dfy** 
Immutable (functional) model to support MutableMapImpl.  API provides an
iterator interface with a deterministic order for parsing/marshaling.
(That's why the API is/ more than just a Dafny map.)

TODO(jonh): Here and elsewhere, Model files seem to be both
API (because callers use some of the definitions as 'public' ways
to reason about the behavior of the modeled Impl) and internal
proof (the logic half of the behavior of the Impl). It would be
nice to cleanly separate these concerns.


**lib/Lang/LinearBox.i.dfy** 

**lib/Base/total_order_impl.i.dfy** 

**lib/Crypto/CRC32Lemmas.i.dfy** 

**lib/Crypto/CRC32Lut.i.dfy** 

**lib/DataStructures/BitmapImpl.i.dfy** 
Maintains a compact set of integers using a packed-uint64 bitmap
representation.


**lib/DataStructures/LinearUSeq.i.dfy** 

**lib/DataStructures/MutableMapImpl.i.dfy** 
A map implemented as a fast, mutable hash table.


**lib/Marshalling/GenericMarshalling.i.dfy** 

**lib/Buckets/PackedStringArray.i.dfy** 

**lib/Buckets/PivotsLib.i.dfy** 

**lib/Crypto/CRC32CArrayImpl.i.dfy** 

**lib/Crypto/CRC32CImpl.i.dfy** 

**lib/DataStructures/BtreeModel.i.dfy** 

**lib/DataStructures/LruModel.i.dfy** 
An LRU-queue.


**lib/Buckets/BucketsLib.i.dfy** 

**lib/Buckets/PackedStringArrayMarshalling.i.dfy** 

**lib/DataStructures/LruImpl.i.dfy** 
An LRU-queue.


**lib/DataStructures/MutableBtree.i.dfy** 

**lib/Buckets/BucketIteratorModel.i.dfy** 
A mathematical description of bucket iterators.
The implementation is defined in BucketImpl together with MutBucket.


**lib/Buckets/BucketWeights.i.dfy** 

**lib/DataStructures/KMBtree.i.dfy** 

**lib/Buckets/BucketModel.i.dfy** 

**lib/Buckets/PackedKV.i.dfy** 

**lib/Buckets/LKMBPKVOps.i.dfy** 

**lib/Buckets/PackedKVMarshalling.i.dfy** 

**lib/Buckets/BucketImpl.i.dfy** 

# Trusted Map Spec

**MapSpec/UI.s.dfy** 

**MapSpec/UIStateMachine.s.dfy** 

**MapSpec/MapSpec.s.dfy** 

**ByteBlockCacheSystem/AsyncDiskModel.s.dfy** 
An async disk allows concurrent outstanding I/Os. The disk is a sequence of bytes.

(Real disks constrain I/Os to fall on logical-block-address boundaries, but we're
ignoring constraint for now.)


**MapSpec/ThreeStateVersioned.s.dfy** 
Our definition of crash-safety.


**Impl/MainDiskIOHandler.s.dfy** DiskInterface

**MapSpec/ThreeStateVersionedMap.s.dfy** 

**Impl/Main.s.dfy** 

# Verified B-epsilon Tree

**BlockCacheSystem/AsyncSectorDiskModelTypes.i.dfy** 

**Betree/Graph.i.dfy** 
An abstract graph that tracks dependencies.
It is an interface implemented by BetreeGraph (and the refined
PivotBetreeGraph): trees whose dependencies are child pointers that
reference other nodes.
It is used by the BlockInterface to identify which blocks can be
garbage-collected because they're unreachable from the graph roots.


**Impl/BucketGeneratorModel.i.dfy** 
A mathematical description of bucket generators.
It's like an iterator, but it doesn't directly refer to an actual bucket.
The bucket may be implicit.


**MapSpec/Journal.i.dfy** 

**PivotBetree/Bounds.i.dfy** 
Defines bounds on various abstract quantities, such as the number
of children of a node.


**Betree/Transactable.i.dfy** 
A Transactable is a state machine defined by atomically gluing together
groups of a few step primitives. Each BetreeSpec operation performs
an atomic sequence of cache updates, such as a block allocation
followed by a write (which includes a reference to the allocated block).


**BlockCacheSystem/DiskLayout.i.dfy** 

**BlockCacheSystem/JournalRange.i.dfy** 

**Impl/BlockAllocatorModel.i.dfy** 
A BlockAllocator tracks which blocks are allocated, to safely allocate
blocks unused by any view.


**Impl/BucketGeneratorImpl.i.dfy** 

**Impl/BucketSuccessorLoopModel.i.dfy** 

**MapSpec/TSJ.i.dfy** 

**Betree/BlockInterface.i.dfy** 
A BlockInterface lets its client code (the Betree) perform atomic sequences
of block allocation (assigning a new value),
block write (replacing an existing value),
and read steps.
It also supports a GC step that frees some subset of unreferenced blocks.


**BlockCacheSystem/JournalInterval.i.dfy** 

**ByteBlockCacheSystem/JournalBytes.i.dfy** 

**Impl/BlockAllocatorImpl.i.dfy** 
A BlockAllocator tracks which blocks are allocated, to safely allocate
blocks unused by any view.


**Impl/BucketSuccessorLoopImpl.i.dfy** 

**MapSpec/TSJMap.i.dfy** 

**Versions/VOp.i.dfy** 

**Betree/BetreeSpec.i.dfy** 
Defines the basic B-e-tree-shaped operations.

* A Query is satisfied by examining enough of the tree to observe a
terminating message list.
* Insert shoves a single message into the root.
* Flush moves a bundle of messages from a node to one of its children.
* Grow inserts a new layer at the top of the tree to admit growth.
* Redirect replaces a subtree with a semantically-equivalent one.
(when do we use that?)


**Impl/JournalistMarshallingModel.i.dfy** 

**Impl/JournalistParsingImpl.i.dfy** 

**MapSpec/TSJMap_Refines_ThreeStateVersionedMap.i.dfy** 

**Versions/JournalView.i.dfy** 

**Versions/StatesView.i.dfy** 

**Betree/Betree.i.dfy** 
Betree lowers the "lifted" op-sequences of BetreeSpec down to concrete state machine
steps that advance the BetreeBlockInterface as required by BetreeSpec.
It also interleaves Betree operations with BlockInterface garbage collection.

TODO(jonh): This probably should get renamed; its place in the heirarchy
is confusing.


**Impl/JournalistMarshallingImpl.i.dfy** 

**Impl/JournalistModel.i.dfy** 

**Versions/StatesViewMap.i.dfy** 

**Betree/BetreeInv.i.dfy** 
Invariants about Betrees: lookup structure, non-equivocation, and
preservation.
TODO(jonh) and apparently a bunch of dead code! See TODO inline.


**Impl/JournalistImpl.i.dfy** 

**PivotBetree/PivotBetreeSpec.i.dfy** 
A PivotBetree refines a Betree, carrying forward the tree structure
but refining the abstract infinite key maps with key ranges separated
by pivot keys.


**Versions/CompositeView.i.dfy** 

**Betree/Betree_Refines_Map.i.dfy** 
Refinement proof from Betree to Map.


**BlockCacheSystem/SectorType.i.dfy** 

**PivotBetree/PivotBetreeSpecWFNodes.i.dfy** 

**Versions/CompositeView_Refines_TSJMap.i.dfy** 

**BlockCacheSystem/BlockDisk.i.dfy** 

**BlockCacheSystem/JournalDisk.i.dfy** 

**PivotBetree/PivotBetreeSpecRefinement.i.dfy** 
Lays out the abstraction function between the datatypes, setting
up for PivotBetree_Refines_Betree.


**Versions/CompositeView_Refines_ThreeStateVersionedMap.i.dfy** 

**BlockCacheSystem/BlockCache.i.dfy** 

**BlockCacheSystem/BlockJournalDisk.i.dfy** 

**BlockCacheSystem/JournalCache.i.dfy** 

**PivotBetree/PivotBetree.i.dfy** 
Like Betree, PivetBetree lowers the "lifted" op-sequences of PivotBetreeSpec
down to concrete state machine steps that advance the PivotBetreeBlockInterface
as required by BetreeSpec. The only difference is that the interface has a more
concrete (pivot-y) type.


**BlockCacheSystem/BetreeCache.i.dfy** 
Bind a Betree to a BlockCache to get the behavior of both: the map implementation of a Betree,
and the crash-safety implementation of a BlockCache.


**BlockCacheSystem/BlockSystem.i.dfy** 

**BlockCacheSystem/JournalSystem.i.dfy** 

**ByteBlockCacheSystem/Marshalling.i.dfy** 

**Impl/CommitterModel.i.dfy** 

**PivotBetree/PivotBetree_Refines_Betree.i.dfy** 

**PivotBetree/StatesViewPivotBetree.i.dfy** 

**BlockCacheSystem/BlockJournalCache.i.dfy** 

**BlockCacheSystem/BlockSystem_Refines_StatesView.i.dfy** 

**BlockCacheSystem/JournalSystem_Refines_JournalView.i.dfy** 

**ByteBlockCacheSystem/InterpretationDiskOps.i.dfy** 

**Impl/CommitterImpl.i.dfy** 

**Impl/IndirectionTableModel.i.dfy** 

**PivotBetree/PivotBetree_Refines_Map.i.dfy** 
Composes the two refinements:

PivotBetree -> Betree
Betree -> Map

To yield

PivotBetree -> Map


**BlockCacheSystem/BetreeSystem.i.dfy** 
Instantiate the {PivotBetree, BlockCache} code in a System (model of the environment).
("Bottom lettuce")


**ByteBlockCacheSystem/ByteCache.i.dfy** 

**ByteBlockCacheSystem/InterpretationDiskContents.i.dfy** 

**Impl/DiskOpModel.i.dfy** 

**Impl/IndirectionTableImpl.i.dfy** 
The heap-y implementation of IndirectionTableModel.


**PivotBetree/StatesViewPivotBetree_Refines_StatesViewMap.i.dfy** 

**BlockCacheSystem/BetreeSystem_Refines_StatesViewPivotBetree.i.dfy** 
Take the whole crash-safe BlockCacheSystem, and constrain it to
run the (Pivot)Betree as its client, thereby yielding a 3-state-crash-safe
Betree. (We'll eventually tie that up the stack to get a 3-state-crash-safe
map.)


**ByteBlockCacheSystem/InterpretationDisk.i.dfy** 

**Impl/CommitterReplayModel.i.dfy** 

**Impl/DiskOpImpl.i.dfy** 

**Impl/StateModel.i.dfy** 
This file represents immutability's last stand.
It is the highest-fidelity representation of the implementation
that can be represented with immutable datatypes.

For example, it has a model of the root bucket which does not exist in
BlockCache.  It also represents indirection table as a map to pairs, rather
than two maps, because real, mutable implementation uses a map to pairs.


**BlockCacheSystem/BetreeSystem_Refines_StatesViewMap.i.dfy** 

**Impl/CommitterReplayImpl.i.dfy** 

**Impl/MarshallingModel.i.dfy** 

**Impl/NodeModel.i.dfy** 

**BlockCacheSystem/BetreeJournalSystem.i.dfy** 

**Impl/IOModel.i.dfy** 

**Impl/NodeImpl.i.dfy** 

**BlockCacheSystem/BetreeJournalSystem_Refines_CompositeView.i.dfy** 

**ByteBlockCacheSystem/ByteSystem.i.dfy** 

**Impl/AllocationReport.i.dfy** 

**Impl/BookkeepingModel.i.dfy** 

**Impl/CacheImpl.i.dfy** 
Implements map<Reference, Node>

TODO(thance): We need a CacheModel, because this is taking too big a leap
from map<Reference, Node>.


**Impl/CommitterAppendModel.i.dfy** 

**Impl/CommitterCommitModel.i.dfy** 

**Impl/CommitterInitModel.i.dfy** 

**BlockCacheSystem/BetreeJournalSystem_Refines_ThreeStateVersionedMap.i.dfy** 

**ByteBlockCacheSystem/ByteSystem_Refines_BetreeJournalSystem.i.dfy** 

**Impl/CommitterAppendImpl.i.dfy** 

**Impl/DeallocModel.i.dfy** 

**Impl/FlushModel.i.dfy** 

**Impl/GrowModel.i.dfy** 

**Impl/HandleReadResponseModel.i.dfy** 

**Impl/HandleWriteResponseModel.i.dfy** 

**Impl/LeafModel.i.dfy** 

**Impl/MkfsModel.i.dfy** 

**Impl/SplitModel.i.dfy** 

**Impl/StateImpl.i.dfy** 

**Impl/SuccModel.i.dfy** 

**ByteBlockCacheSystem/ByteSystem_Refines_ThreeStateVersionedMap.i.dfy** 

**Impl/FullImpl.i.dfy** 

**Impl/MarshallingImpl.i.dfy** 

**Impl/SyncModel.i.dfy** 

**Impl/EvictModel.i.dfy** 

**Impl/IOImpl.i.dfy** 

**Impl/Mkfs.i.dfy** 

**Impl/BookkeepingImpl.i.dfy** 

**Impl/CommitterCommitImpl.i.dfy** 

**Impl/CommitterInitImpl.i.dfy** 

**Impl/FlushPolicyModel.i.dfy** 

**Impl/QueryModel.i.dfy** 

**Impl/DeallocImpl.i.dfy** 

**Impl/FlushImpl.i.dfy** 

**Impl/GrowImpl.i.dfy** 

**Impl/HandleReadResponseImpl.i.dfy** 

**Impl/HandleWriteResponseImpl.i.dfy** 

**Impl/InsertModel.i.dfy** 

**Impl/LeafImpl.i.dfy** 

**Impl/SplitImpl.i.dfy** 

**Impl/CoordinationModel.i.dfy** 

**Impl/SyncImpl.i.dfy** 

**Impl/EvictImpl.i.dfy** 

**Impl/SuccImpl.i.dfy** 

**Impl/FlushPolicyImpl.i.dfy** 

**Impl/QueryImpl.i.dfy** 

**Impl/InsertImpl.i.dfy** 

**Impl/CoordinationImpl.i.dfy** 

**Impl/MainHandlers.i.dfy** 

