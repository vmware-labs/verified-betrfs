# Coordination between Journal and Map

This directory contains the CoordinationSystem and its refinement, which shows
a journal and an abstract map data structure are coordinated to give rise to
the spec semantics.

That system takes an abstract JournalIfc as input. A JournalIfc exposes an
"API" (specific enabling conditions and transitions that we expect the implementation
to support efficiently) and a very simple MsgHistory interpretation (which of course never
gets reified in the implementation).  To understand the proof development, we
plug the AbstractJournal into the JournalIfc; it datatype is simply the MsgHistory.
(The final proof doesn't need the AbstractJournal at all; it just helped me develop
the CoordinationSystem, and it may help new people understand it in isolation).

The CoordinationSystem is a "system" because it models crashes and recovery; we'll eventually
show that the (trusted) system model with disk and crashes refines to an
instance of this system, which (via this refinement) is known to implement the CrashSafeMap spec.

The primary challenge in the proof of the CoordinationSystem is developing an "algebra"
of StampedMaps and MsgHistorys: For example, M1+(J1+J2) == (M1+J1)+J2: journal concatenation
is associative with applying a journal to a map.


# The Paged Journal

Because the refinement works against this abstract JournalIfc, it works against
any implementation. This directory also contains a "refined" PagedJournal.
This is a Dafny module refinement (implementation of JournalIfc), not a TLA+-style state
machine refinement. That's because we aren't doing anything new with the state machine
(reusing the CoordinationSystem entirely), only the data structure and its algebra.
(Although the implementations of the JournalIfc APIs can be seen as "refining" the
state machine since they introduce new, tighter enabling conditions.)

The PagedJournal implements the MsgHistory interpretation out of a linked list of journal
pages, arranged as we expect the implementation to be arranged: A list of immutable records
plus a head record with the "boundary LSN" that tells us when to stop reading the linked
list (even before we get to a None pointer).

The primary challenge in the proof of the PagedJournal is developing a quanified "receipt"
that explains how a linked list gets interpreted, and then an algebra of operations on
linked lists and their receipts to enable them to be manipulated while maintaining the
desired MsgHistory interpretations.

# Next steps:

* Breadth-first: A paged map! This is much fancier; we should start with a paged B+ tree.

* Depth-first: A cached journal. Explain how linked list pages get assigned to cache addresses
and how pointers get dereferenced. Add a notion of failed reads (malformed records) to extend
the notion of TJ-invalidity in the higher layer. Receipts at this layer will also need to track
what cache pages they access -- even for decodings of invalid TruncatedJournals -- because
we'll need that to manage framing in a layer below.

