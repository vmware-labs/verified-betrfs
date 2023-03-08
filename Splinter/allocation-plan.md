# Allocation state

At the allocation layer, we want to satisfy allocation requests quickly
by consulting a small, in-memory FreeSet of AUs.

## Freeing

To avoid leaking pages, AUs need to reappear in the FreeSet when they're
no longer in use.

We allocate from the intersection of the Persistent, In-flight, and Ephemeral
FreeSets, so freeing unused pages when a Persistent disk is replaced by an
in-flight is trivial: Simply drop the old persistent FreeSet.

The ephemeral state, on the other hand, can be mutated, so we need a way
to replace AUs in the Ephemeral FreeSet when they're no longer referenced
by the Ephemeral superblock. For this, we track references counts at a
coarse grain using small, in-memory reference-count tables.
Coarse-grained means that reference counts are tracked at the AU level,
and that we track different data structures differently.
* BeTree nodes are reference counted directly.
* B+Tree roots are reference counted. Once linked into the superblock,
a B+Tree is immutable, so it carries an on-disk summary so that a single
reference can cover the hundreds of AUs that comprise the branch tree.
* Journal AUs are tracked in memory with a relation to LSNs, so that
when an in-flight superblock lands, a long stripe of AUs (probably most of
the journal) can be dereferenced without reference to the actual journal
blocks.

# Participating variables & ghost functions

## B+Tree

* B+RC (real): The AU-level reference count for B+Tree roots

* B+Alloc (ghost function of B+ diskview): maps a root pointer to the set of AUs
  reachable from that root.

## BeTree

* BeRC (real): The AU-level reference count for BeTrees

## Journal

* JAULSN (real): a relation between AU and LSN (summarized by ranges to exploit
  contiguity).

* JRC (ghost function of JAULSN): set of AUs in JAULSN

## AllocatorCoordination

* FS: An AU-level Free Set


# Invariants

- BeRC !! B+RC !! JRC !! B+Alloc !! FS partition the disk
  - tells us that when we grab an au from FS, it's not in any other set

- ProjectPages(BeRC + B+RC + JRC + B+Alloc) >= likes (pages from the layer above)
  - tells us that the AU we grabbed from FS has no pages that are liked
  (and thus mutating it would break the interpretation of anything reachable
  from the current ephemeral superblock).

# State machine composition plan

The single FS (free set) interacts both journal and tree, and thus belongs
in a CoordinationSystem, which means we have to terminate the independent
refinement stacks of Tree and Journal at this level.

The proposed structure is:

- AllocationCoordinationSystem
  - FS variable
  - AllocationCrashTolerantTree
    - AllocationTree
      - BeRC variable
      - B+RC variable
      - B+Alloc *ghost* variable
      - ghost LikesBranchedBetree
  - AllocationCrashTolerantJournal
    - AllocationJournal
      - JAULSN (Journal-AU-LSN-relation) -- provides JRC by projecting away LSNs
      - ghost LikesJournal
      - mini-allocator for Journal

# Mini-allocation

AllocationJournal Variables contains a new in-memory field
  miniallocator: set<Addr>
that is a set of page-level addresses that have been claimed from FS.
Which partition are they in?
Once the first page is used and linked into the superblock, they're
covered by an AU-level refcount.

- Maybe the easiest thing is to instantaneously refill the miniallocator
  only at the moment we need it and can link it.

- Another possibility is to add a new partition JAlloc for AUs mini-allocated
  (moved out of FS) but not yet linked into the data structure (and therefore
  recoverable by the JRC).

## State of mini-allocation

The mini-allocator state for the Journal (as an example) is:

  * AllocatedAUs: a set of AUs removed from the free set but still unused.
  (It would be safe to return any of these to the free set.)

  * UsunedPages: a set of pages that each belong to an AU that's part of
  the Journal RC (because another page from the AU is in the Journal Repr),
  but this page is unused.

## Phases of mini-allocation

1. The ephemeral Journal has some chain of pages in its repr; the projection
    of those pages is reflected in JRC. AllocatedAUs and UnusedPages is empty.

2. An AU leaves the FreeSet and enters the AllocatedAUs.

    If we freeze here, entries in this set are returned to the
    free set, since their AUs are not reachable from the repr graph.
    In the refinement, these pages are treated as free.

3. An AU leaves AllocatedAUs and enters JRC when its first page is linked
    into the ephemeral journal graph and thus into the ephemeral superblock
    graph.

    Its remaining pages are recorded in UnusedPages. The semantics
    of this set are that these pages are known by invariant

    * to not be linked into the persistent, in-flight, or ephemeral view of any
      non-journal data structure: because that's true of every page in every AU
      in JRC.

    * to not be linked into the persistent, in-flight, or ephemeral view of the
      journal: because that's the new invariant associated with UnusedPages.

    If we freeze here, persist, and crash, any pages in UnusedPages
    become "stranded": they're not part of a repr, but the AU they belong to
    is claimed by the journal. Such pages will stay in this state until
    the containing AU eventually dropped when the persistent state is dropped
    as a new frozen state lands.

4. When the journal needs another page, the mini-allocator removes the page
     from UnusedPages in the same atomic step that links the page into the
     journal's repr.

# Recovery

The first step of recovery is to reconstruct all of the partitions.
There's an atomic step RecoverAllocationMetadata that does this.
It assumes all the necessary pages are faulted into memory, and then
takes a step that records the in-memory BeRC, B+RC, JRC, returns B+Alloc,
and computes the complemement of them as FS.

One discussion we had was whether this step could really be atomic in
the implementation, or whether we needed to break it up into an induction
that's visible in a lower state refinement layer with a linearization
point at the end that exposes the inductively computed result.

We don't think that's worth the trouble, as long as all the state necessary
to compute that atomic step can be fit in the cache at once. It should:

## Journal memory demand

The journal needs to see one page for each AU: the page that points into the
next AU. It can infer (via invariant) that the pages chain together until
they reach page 0 of that AU, which is the one that points out into another
AU and thus must be in cache.

The journal should be sized about 10x the cache size. 10x captures 90%
of the write-amplification-reduction benefit of the journal; further growth
has diminishing returns.

If an AU is 128kB and a page is 4kB, then the AU:page ratio is 32, and thus
journal recovery requires filling 10/32 (about a third) of the cache.

## Tree memory demand

To observe the tree usage, we need to see every trunk (BeTree) node
and the statically-captured index of reachable AUs at the root of every B+Tree.

If an AU is an 8-byte value, then a page can store 512 AU refereces, which
for 128kB AUs is 64MB. Let's assume that we need to visit a small number $k$
of pages (1-3) for each B+tree.

Furthermore, the ratio of B+Trees (branch) to BeTree (trunk) nodes is
approximately constant, driven by an implementation policy of flushing any
BeTree node before its branch buffer stack exceeeds some height $l$. Flushed
branches are multiply referenced by fanout $f$ children, so there are $l/f$
branches per trunk node. We suppose $l/f$ will be small (1-3), since accumulating
tall buffer stacks offers no performance benefit.

Almost all of the data on a disk is in branches.
When $k=3$ branches contain 192MB.
A 10TB disk would contain 52K branches.
Recovery would require visiting one BeTree page + $k * l/f$ BeTree AU indices.

Plugging in some concrete values:
* 10TB disk, $k=3$, $l/f=3$ requires 1.4GB
* 10TB disk, $k=1$, $l/f=3$ requires 3.1GB
* 1TB disk, $k=1$, $l/f=3$ requires 0.3GB

## Recovery Conclusion

We can safely defer the matter of induction during refcount/free set recovery
into a single amotic step; the induction variables and invariants can hide
inside an implementation while loop that scans a locked cache.

(Note we said "driven by an implementation policy" above. For now we're not
proving recoverability; an adversarial implementation could build a disk full
of teensy B+trees such that recovery demands exceed the cache size.)

