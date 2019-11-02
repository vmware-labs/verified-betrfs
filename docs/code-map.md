# Specification
* disk-betree/ThreeStateVersionedMap.s
* disk-betree/Main.s
* disk-betree/ThreeStateVersioned.s
* disk-betree/MainDiskIOHandler.s
* disk-betree/AsyncDiskModel.s
* disk-betree/UI.s
* disk-betree/UIStateMachine.s
* disk-betree/MapSpec.s

# Implementation (toposorted)



**disk-betree/Message.i.dfy**  The messages propagated down a B-epsilon tree. Each message either completely defines the value of the key, or is a delta that modifies the value defined by prior messages. 

**disk-betree/Bounds.i.dfy**  This file defines bounds on various abstract quantities, such as the number of children of a node. 

**disk-betree/Graph.i.dfy**  An abstract graph that tracks dependencies. It is an interface implemented by BetreeGraph (and the refined PivotBetreeGraph): trees whose dependencies are child pointers that reference other nodes. It is used by the BlockInterface to identify which blocks can be garbage-collected because they're unreachable from the graph roots. 

**disk-betree/AsyncSectorDiskModel.i.dfy**  An AsyncSectorDisk is a disk (map from Location to Sector) that interleaves concurrent in-flight requests. 

**disk-betree/PivotsLib.i.dfy**  Provides definitions and libraries for pivot tables. A pivot table is a sorted list of *pivot* keys that divides the keyspace into contiguous ranges. 


**disk-betree/Transactable.i.dfy**  A Transactable is a state machine defined by atomically gluing together groups of a few step primitives. Each BetreeSpec operation performs an atomic sequence of cache updates, such as a block allocation followed by a write (which includes a reference to the allocated block). 

**disk-betree/BlockAllocator.i.dfy**  A BlockAllocator tracks which blocks are allocated, to safely allocate blocks unused by any view. 

**disk-betree/BucketsLib.i.dfy**  A Bucket maps keys to Messages. A BucketList imparts a Message meaning to every key obeying the Message composition rules. This module shows how pushing messages down a tree towards a child still produces equivalent values as viewed through the Message chain. 


**disk-betree/BucketWeights.i.dfy**  Assigning weights to buckets guides the flushing algorithm to decide which child to push messages towards. TODO(thance): help! 

**disk-betree/BlockInterface.i.dfy**  A BlockInterface lets its client code (the Betree) perform atomic sequences of block allocation (assigning a new value), block write (replacing an existing value), and read steps. It also supports a GC step that frees some subset of unreferenced blocks. 


**disk-betree/BetreeSpec.i.dfy**  Defines the basic B-e-tree-shaped operations. * A Query is satisfied by examining enough of the tree to observe a terminating message list. * Insert shoves a single message into the root. (Do we still use that, now that we have a mutable write buffer at the top?) * Flush moves a bundle of messages from a node to one of its children. * Grow inserts a new layer at the top of the tree to admit growth. * Redirect replaces a subtree with a semantically-equivalent one. (when do we use that?) 

**disk-betree/KVList.i.dfy**  A list of key-message pairs, with unique, sorted keys. TODO(robj,thance): How is it used... in MutableBucket? 


**disk-betree/Betree.i.dfy** 

**disk-betree/KVListPartialFlush.i.dfy** 


**disk-betree/BetreeInv.i.dfy** 

**disk-betree/PivotBetreeSpec.i.dfy** 

**disk-betree/MutableBucket.i.dfy** 


**disk-betree/Betree_Refines_Map.i.dfy** 

**disk-betree/PivotBetree.i.dfy** 

**disk-betree/PivotBetreeSpecRefinement.i.dfy** 

**disk-betree/BlockCache.i.dfy** 


**disk-betree/BlockCacheSystem.i.dfy** 

**disk-betree/PivotBetree_Refines_Betree.i.dfy** 

**disk-betree/ThreeStateVersionedPivotBetree.i.dfy** 

**disk-betree/BetreeBlockCache.i.dfy** 


**disk-betree/BlockCacheSystem_Refines_ThreeStateVersionedBlockInterface.i.dfy** 

**disk-betree/IndirectionTableModel.i.dfy** 

**disk-betree/PivotBetree_Refines_Map.i.dfy** 


**disk-betree/IndirectionTableImpl.i.dfy** 

**disk-betree/ImplModel.i.dfy** 

**disk-betree/BetreeBlockCacheSystem.i.dfy** 


**disk-betree/ImplMarshallingModel.i.dfy** 

**disk-betree/BetreeBlockCacheSystem_Refines_ThreeStateVersionedPivotBetree.i.dfy** 


**disk-betree/Marshalling.i.dfy** 


**disk-betree/ByteBetreeBlockCache.i.dfy** 


**disk-betree/ByteBetreeBlockCacheSystem.i.dfy** 

**disk-betree/ImplModelIO.i.dfy** 


**disk-betree/ImplModelCache.i.dfy** 

**disk-betree/ByteBetreeBlockCacheSystem_Refines_BetreeBlockCacheSystem.i.dfy** 


**disk-betree/ImplModelDealloc.i.dfy** 

**disk-betree/ImplModelSplit.i.dfy** 

**disk-betree/ImplModelFlush.i.dfy** 

**disk-betree/ImplModelQuery.i.dfy** 

**disk-betree/ImplModelLeaf.i.dfy** 

**disk-betree/ImplModelGrow.i.dfy** 


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


**disk-betree/ImplGrow.i.dfy** 

**disk-betree/ImplDealloc.i.dfy** 

**disk-betree/ImplLeaf.i.dfy** 

**disk-betree/ImplSplit.i.dfy** 

**disk-betree/ImplFlush.i.dfy** 


**disk-betree/ImplSync.i.dfy** 


**disk-betree/ImplQuery.i.dfy** 

**disk-betree/ImplEvict.i.dfy** 


**disk-betree/ImplFlushPolicy.i.dfy** 


**disk-betree/ImplInsert.i.dfy** 


**disk-betree/MainImpl.i.dfy** 


# Libs
## missing Dafny math & data structure behavior
* lib/Sets.i
* lib/MutableMapModel.i
* lib/MutableMapImpl.i
* lib/SetBijectivity.i
* lib/BitsetLemmas.i
* lib/Bitmap.i
* lib/Math/bases.i
* lib/Marshalling/Maps.i
* lib/Marshalling/Math.i
* lib/Marshalling/Util.i
* lib/Marshalling/MarshallInt.i
* lib/mathematics.i
* lib/tttree.i
* lib/LRU.i

## Marshalling
* lib/Marshalling/GenericMarshalling.i

# Axiom libs
## Data structures used in spec
* lib/Option.s
* lib/Maps.s

## New math for KV stores
* lib/total_order.s
* lib/Crypto.s

## missing Dafny data structure behavior
* lib/sequences.s
* lib/Marshalling/Seqs.s - not sure why it's .s
* lib/Marshalling/Seqs.i

## faster implementation
* lib/Marshalling/Native.s
* lib/NativeTypes.s
