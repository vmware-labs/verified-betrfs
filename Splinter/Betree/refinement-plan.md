# Refinement Plan

* PagedBetree

Goal: most abstract tree structure

    * Functional (no pointers)

    * complete AnyKey child maps (no pivots)

    * BufferStack is seq of inline map<key,message> buffers (from BufferStackMod)

    * Flushing rewrites buffers


* PivotBetree

Goal: replace infinite children with finite pivots.

    * Functional (no pointers)

    * child pivot table (finite)

    * BufferStack is seq of inline map<key,message> buffers (from BufferStackMod)

    * Flushing rewrites buffers

* FilteredBetree

Goal: Avoid rewriting buffers during flush using a flushedOffsets table

    * Functional (no pointers)

    * child pivot table (finite)

    * BufferStack is seq of inline map<key,message> buffers (from BufferStackMod)

    * flushedOffsets index; buffers flushed without mutation
  

* LinkedBetree

Goal: Reason about indirection and hence acyclicity
TODO: How do we account for dropping last ref to a buffer?

    * Two DiskViews: BetreeNodes and Buffer-in-a-Block DiskView

    * child pivot table (finite), each is an Address

    * BufferStack is seq<Address> (from LinkedBufferStack)

    * flushedOffsets index; buffers flushed without mutation


* BranchedBetree

Goal: Account for the fact that buffers actually occupy many addresses.

    * Two DiskViews: BetreeNodes and a forest-of-Branches DiskView

    * child pivot table (finite), each is an Address

    * BufferStack is seq<Address> (from LinkedBufferStack)

    * flushedOffsets index; buffers flushed without mutation


* LikesBranchedBetree

Goal: Enable transitions that can free referents without observing entire data
structure on disk (via maintenance and use of in-memory index).

    * Two DiskViews: BetreeNodes and a forest-of-Branches DiskView

    * child pivot table (finite), each is an Address

    * BufferStack is seq<Address> (from LinkedBufferStack)

    * flushedOffsets index; buffers flushed without mutation

    * Adds in-memory refcount indices for refs to betrees, branches


* AllocationBranchedBetree (In this layer we want to tie the coordination system together)

Goal: Lift page-level reference counts into AU-level reference counts

    * Two DiskViews: BetreeNodes and a forest-of-Branches DiskView

    * child pivot table (finite), each is an Address

    * BufferStack is seq<Address> (from LinkedBufferStack)

    * flushedOffsets index; buffers flushed without mutation

    * Adds in-memory refcount indices for AU-refs to betrees, branches

    * Adds MiniAllocator for tracking reserved pages for branches.
