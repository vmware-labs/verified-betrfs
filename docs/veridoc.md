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

**lib/Marshalling/Seqs.i.dfy** 

**lib/Marshalling/Util.i.dfy** include "../../Common/Native/Io.s.dfy"

**lib/Sets.i.dfy** 

**lib/tttree.i.dfy** 

**lib/Bitmap.i.dfy** NOTE: requires /noNLarith

**lib/Marshalling/MarshallInt.i.dfy** include "../../../Libraries/Util/seqs_transforms.i.dfy"

**lib/MutableMapModel.i.dfy** 

**lib/Marshalling/GenericMarshalling.i.dfy** 

**lib/MutableMapImpl.i.dfy** 

**lib/LRU.i.dfy** A LRU-queue.

# Trusted B-epsilon Tree

**disk-betree/UI.s.dfy** 

**disk-betree/UIStateMachine.s.dfy** 

**disk-betree/MapSpec.s.dfy** 

**disk-betree/AsyncDiskModel.s.dfy** 

**disk-betree/ThreeStateVersioned.s.dfy** 

**disk-betree/MainDiskIOHandler.s.dfy** DiskInterface

**disk-betree/ThreeStateVersionedMap.s.dfy** 

**disk-betree/Main.s.dfy** 

# Verified B-epsilon Tree

**disk-betree/AsyncSectorDiskModel.i.dfy** 
An AsyncSectorDisk is a disk (map from Location to Sector) that interleaves
concurrent in-flight requests.


**disk-betree/Bounds.i.dfy** 
This file defines bounds on various abstract quantities, such as the number
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

**disk-betree/KVListPartialFlush.i.dfy** 

**disk-betree/BetreeInv.i.dfy** 

**disk-betree/MutableBucket.i.dfy** 

**disk-betree/PivotBetreeSpec.i.dfy** 

**disk-betree/Betree_Refines_Map.i.dfy** 

**disk-betree/BlockCache.i.dfy** 

**disk-betree/PivotBetree.i.dfy** 

**disk-betree/PivotBetreeSpecRefinement.i.dfy** 

**disk-betree/BetreeBlockCache.i.dfy** 

**disk-betree/BlockCacheSystem.i.dfy** 

**disk-betree/PivotBetree_Refines_Betree.i.dfy** 

**disk-betree/ThreeStateVersionedPivotBetree.i.dfy** 

**disk-betree/BlockCacheSystem_Refines_ThreeStateVersionedBlockInterface.i.dfy** 

**disk-betree/IndirectionTableModel.i.dfy** 

**disk-betree/PivotBetree_Refines_Map.i.dfy** 

**disk-betree/BetreeBlockCacheSystem.i.dfy** 

**disk-betree/ImplModel.i.dfy** 

**disk-betree/IndirectionTableImpl.i.dfy** 

**disk-betree/BetreeBlockCacheSystem_Refines_ThreeStateVersionedPivotBetree.i.dfy** 

**disk-betree/ImplMarshallingModel.i.dfy** 

**disk-betree/Marshalling.i.dfy** 

**disk-betree/ByteBetreeBlockCache.i.dfy** 

**disk-betree/ByteBetreeBlockCacheSystem.i.dfy** 

**disk-betree/ImplModelIO.i.dfy** 

**disk-betree/ByteBetreeBlockCacheSystem_Refines_BetreeBlockCacheSystem.i.dfy** 

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

