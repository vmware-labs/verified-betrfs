# How to model shared-nothing concurrency

This section describes how the IronFleet system exploited shared-nothing concurrency
by sharding state across hosts in a message-passing system. The basic idea follows
the state-machine refinement modeling recommended by the TLA+ specification methodology.

One of the two distributed systems verified in IronFleet was a sharded
hash table (SHT). The IronFleet sharded hash table was a simple (non-replicated)
key-value store in which a set of peer nodes partitioned responsibility for the buckets of a
hash table. Each node ran a single-threaded server program. Each key hashed to
a bucket. Each bucket was assigned to a node.

To read or write a key, node A would first acquire the bucket. The protocol involved
first sending a hint message to the current owner B of the bucket.
(I don't recall how nodes discovered or updated the ownership mapping hint table.)
The current owner B would transmit a message to A that represented the lock on the bucket
and carried the key-value pairs that hashed into the bucket.
IronFleet SHT assumed (implemented?) a reliable message delivery layer.
When the message was received at A, A recorded the data and the fact that it now owned
the bucket.

Presumably sets or ranges of buckets could be transmitted in a single message.
A node could effect a transaction by arranging to hold all of the necessary buckets,
and then implementing the transactional update in a local atomic step.

## Correctness intuition

Intuitively, every key-value pair had a single bucket to live in, and every bucket
had a place to live: typically a node, but between transmission and reception of
a bucket transfer, it "lived" in the (reliable) network layer.
Although operations were being executed concurrently across nodes in the system,
the IronFleet reduction argument let us think about an arbitrary interleaving
of atomic steps.

Each atomic user-visible put or get operation refined to an atomic put or get
in a centralized state machine model. Think of it as though we were transferring
*every* bucket to each node just before that node's turn in the serialization order.
Not-transferring most of the buckets in the real implementation was merely an optimization.

Each bucket transfer refined to a no-op.

## Verification scheme

The intuition above sketches the basic refinement proof structure:
The application specification was a "centralized" state machine model: a dictionary
with all the key-value pairs. Each user request arrives (establishing the early limit
of its serialization point), occurs atomically with respect to every other user
request (the serialization point), and is ultimately acknowledged (establishing the
late limit of its serialization point). Such a spec allows requests whose occupancy overlap
to be serialized in either order.

The Protocol layer consisted of a (trusted) distributed system spec that
composed the (trusted) network model with *n* copies of the (verified) program
model, called the Host state machine.  Each Host was an atomic state
machine implementing the protocol above: the program state consisted of an
"ownership table" of which buckets (key ranges) are managed at this host, plus
the key-value pairs known to exist in those buckets. Actions (transitions)
included the sending and receipt of bucket transfer messages and the execution
of user operations, conditioned on the Host having ownership over the buckets
covered by each operation.

### Implementation refinement

The imperative code was a straightforward implementation of the Protocol layer
with a correspondingly straightforward refinement proof obligation.
A (trusted) main function called a (verified) initialization routine and then,
in an infinite loop, called a (verified) handler. The handler code
provided an interpretation function that mapped its local state to a Host state.
Each invocation of the handler is shown (via Hoare logic) to transform its
local state in a way such that the interpretations of the before- and after-states
are valid transitions of the Protocol Host state machine.

The (verified) main loop controlled access to the network so as to enforce an
ordering condition required to support the (paper-and-pencil) reduction argument that
concurrent execution of handlers on multiple hosts was equivalent to sequenced
execution, so that modeling the handlers as "atomic" steps in the Protocol layer
was valid.

### Protocol refinement

This imperative-to-protocol strategy was straightforward in that it would work the
same way with any distribution (concurrency) scheme. The interesting concurrency
reasoning happened in the upper refinement, from the Protocol layer to the application
spec.

The key to every refinement proof is its interpretation function. In this case, the
interpretation function simply took the union of the buckets from hosts and the
network.
More precisely: the interpretation map included a key-value
mapping if either it appears at some host or it appears in a transfer message
that has been sent but not receieved.

This definition isn't well-defined if a key is defined in multiple places; for example,
if (K,3) appears at one host, but (K,5) also appears in an outstanding message.
In such situations, we define the interpretation to choose a tuple arbitrarily from
those available.
Then we show as an inductive invariant that the choice is never free; that is,
in every reachable state, a key appears in a single place: either a single host,
or in a single outstanding network message.

Given this structure and invariant, the remainder of the refinement proof falls
out simply. Sending a transfer message refines to a stutter step (no-op) in the spec:
Every key in the message atomically disappears from the sending host and reappears
in a fresh outstanding message, bound to the same value. Likewise, transfer receipts
preserve the invariant and refine to a stutter.

The Protocol conditions a user operation on local ownership of a bucket, making
its refinement simple: the distributed Host computes the same answer required by
the interpreted atomic state machine, *even though it doesn't know most of the
values of the hash table*.

Ownership is the central concurrenty strategy for this system.
If a Hosts didn't track which buckets it owns, it might answer Get(K) with "empty",
even if K were known at another host.
Or if a Host initiated a transfer of (K,3), but kept a copy of (K,3) around locally,
and then accepted Put(K,4), users could get divergent answers to Get(K) forever, even
if K was never again modified.

# The connection between distributed sharding and locking

If you squint, you can view the IronFleet sharded hash table as a lock-based system.
Each Host is a thread.
The network's buffer of outstanding messages represent unlocked buckets.
Receiving an outstanding message and recording ownership over it is lock acquisition.
Transmitting a new transfer message and relinquishing ownership over it is lock release.

The locking discipline is very simple: the hash table is chained, in that each key fits
in the bucket its hash routes it to. In fact, in the distributed model, there's no
need to even hash keys; buckets can be labeled with a key range.
Later, we'll consider more elaborate locking disciplines.

# How to model shared-memory concurrency

We can realize the "squint" observation to verify a multi-threaded
shared memory concurrent system.
**For pedagogy, we should actually build the trivial-locking system I begin with here.**

The system follows a very similar refinement structure.
The application specification at the top is identical.
At the bottom, a (trusted) main function calls a (verified) initialization function,
instantiates many threads, and on each thread calls a (verified) handler function.
The init function creates an empty data structure behind mutexes,
then returns a value type containing references to the mutexes
which ```main``` distributes to the handler threads.

In the middle, analogous to the Protocol state machine, the developer builds
a *sharded state machine model* of the threaded computation.

Going up, an interpretation function maps the whole state machine (as the union of all the shards)
to the application spec. The corresponding refinement proof shows how atomic steps
of the Protocol model refine to valid transitions of the application spec.

From the bottom, the imperative handler is shown to manipulate mutexes and the data
behind them in a way that refines to some subset ("shard") of the Protocol model.

A (trusted) mutex implementation and a linear type system enforces that protected
data are only accessible by one thread at a time; lock acquisition brings a mutex-protected
datum "into" a thread's shard, corresponding to message delivery in the IronFleet.

The mutex implementation furthermore enforces a (verified) application-specified invariant.
This invariant enables the implementation to relate the physical contents of a mutex to
a ghost shard of the Protocol sharded state machine. A thread uses this invariant to demonstrate
that its answers to application requests are consistent with those required by the Protocol
state machine (and hence the application spec itself). The mutex spec demands that
threads releasing a mutex establish the invariant so that threads acquiring the mutex
can rely on it.

Note that, while a thread is holding a mutex, it can scramble the physical memory protected
by the mutex however it likes. The mutex contract only requires that, when released, the
physical memory is connected to its ghost representation as specified in the invariant.
This decoupling enables the Protocol layer to reason only about the ghost shards, which
effectively only change at each mutex release, and therefore ignore the fine-grained interleavings
of the physical thread states. The intuition for why this decoupling is sound is analogous to the
reduction argument in IronFleet: other threads can only observe this thread through lock release
and acquisition (transfer message send and receipt). If that communication channel is appropriately
constrained, a thread's local behavior is irrelevant to concurrency, because a thread's actions
are equivalent to a version reduced to an atomic step.
*TODO: is there a reduction underneath here? Is there a requirement that we not release-then-acquire?
Or no, because we have a stronger constraint? There surely must be some refinement argument?*

The thread must still obey the protocol when interacting with other threads (respectively, sending transfer messages)
to ensure the global invariant of the Protocol layer. And it must obey the protocol when revealing values to the user,
which combined with the invariant ensures that the values it reveals refine to the values allowed by the Protocol layer.

## Verification Structure

Let us model an equivalent system.
In the dsitributed setting, the Protocol machine was the lynchpin that connected the simple local implementation
refinement to the concurrent-state-machine reasoning.
The equivalant structure in the shared-memory setting is a ``sharded state machine.''
This is a verified state machine whose state variable type has the additional constraint of being a *commutative monoid*.
That means that the state can be viewed as a ``bag of tokens'' that can then be partitioned across the participating
threads. Mutexes will move the tokens around between threads, linear types will ensure they're conserved,
and the upper-level refinement proof may safely model the entire multi-thread system as if all the tokens are in a
single bag, being manipulated according to the Next transition defined over the state.

When this property is established, the trusted infrastructure exposes the ``shards'' by giving each a ``bag''
in which to hold tokens. The tokens may be passed to other threads through mutexes (via the mutex invariant).
A trusted axiom allows a thread to exchange a bag of tokens for another whenever the exchange obeys the state
machine.

*Boy it's really time for a concrete example and a figure.*

TODO I think we should build the open-addressing table in the IronFleet setting! Can we boil all these
state machines down to compact figures so readers can compare them straight across?

TODO we should also do Robin Hood hashing, but with a simple state machine that requires you hold all the
relevant locks to move atomically.

## A richer locking strategy

The example above is very simple to reason about because the locking strategy is coarse-grained: a thread needs a single
mutex to execute any given Put or Get request. Next we discuss a richer strategy with richer dependencies between the
threads.

Suppose we wanted to do Robin Hood hashing, a form of open-addressing hashing. In this scheme, each hash table entry
has space for a single key-value pair. If a key is already present when a new key is inserted, *one* of the keys must
be pushed down farther into the hash table. That implies that a query must scan some number of entries from the
hash of a key before it can conclude that a key is absent. In Robin Hood hashing, the rule is that, when two keys want
to occupy the same entry, the key whose hash value is lower (closer to the entry index) takes the spot.
That means that a query can terminate its scan with "key absent" as soon as it encounters a key that hashes greater than
the query key.
Insert may require shifting keys out of the way for the new one, and Remove may require contracting keys to fill a gap
so that the query rule can still find them.

User operations in open addressing require reasoning about multiple hash table entries.
The simplest way to do so is to reason about them atomically.
In the distributed setting, this means requiring a host to gather all of the necessary entries to itself,jj0
and then take a single atomic step. For exmaple, when querying an absent key,
the enabling condition identifies a sequence of entries from hash(k) to an empty entry
or one that holds a key that hashes after k, and confirms that k doesn't appear in that range.
That's expressed as a quantified statement in a single step of the Host state machine.
For each entry in the quantified range, the host must own the entry, and the entry's content must satisfy the
Robin Hood query conditions just described.

Note that, in either model, the ownership (lock) granularity is left to the implementation layer.
The distributed system might transfer ownership in blocks of ten entries at a time;
the shared-memory system might use one mutex to protect each block of ten entries.

The equivalent representation in the shared-memory setting is nearly identical:
the enabling condition requires that the thread "owns" a subsequence of entries (holds the corresponding tokens),
and that the entries satisfy the Robin Hood query conditions.
Owning the tokens is what forces the implementation thread to hold (at least) the mutexes protecting the relevant rows.
In either representation, the protocol-level state machine limits the degree of available concurrency: if a query
demands observing a long subsequence of entries, the implementation must gather and lock all of those entries
simulataneously.

## An even finer-grained locking strategy

Suppose we wish to relax the constraint that a host (thread) must lock an entire subsequence of entries concurrently,
to expose greater concurrency: We want an insert thread to be able to begin scanningt entries that a query thread
has already observed, even before the query thread has reached the end of its scan.

(This structure may feel a little contrived. In the distributed case, the cost
of transferring data around is so great, and the cost of inspecting entries
during scans so little, that this concurrency strategy is unlikely to offer
benefit.  In fact, in either case, if hash chains are getting long enough to
create contention, the hash table is surely overloaded. However, this structure
provides an opportunity to study a hand-over-hand locking strategy in a
simplified setting. This strategy is valuable in tree structures with
long-running updates.)

Consider a query that has scanned a dozen entries past hash(k), but hasn't yet reached one containing k
or an entry that proves its absence.
If a remove(k2) operation were to run past the in-progress query, it could change the shape of the hash table,
so that the query observes a prefix from before the insert and a suffix from after.
Specifically, the remove might shift k from beyond the query's pointer to before, so that the query erroneously
concludes that k is absent.
The query and remove operations are unserializable: neither ordering justifies
the results exposed by the operations.

The typical way to expose such concurrency safely is with a hand-over-hand locking strategy,
which requires each in-flight operation to lock the next entry in the sequence before releasing the prior.
Since every operation moves "forward" through the table, no operation can pass by another.
In interpreting each operation, we can declare the serialization point to be the moment it takes its
first lock, since it will necesarily observe the results of every operation that has already begun locking
entries.

Notice that the developer must make an explicit tradeoff to expose greater concurrency; in exchange,
they must introduce greater implementation and reasoning complexity. While the framework may hide concurrency
among atomic steps at the protocol level (reduction in the distributed setting; monoidially in the shared-memory setting),
the developer must reason explicitly about the concurrency strategy above that, since the argument is tightly
integrated with the shape of the data structure being designed.

To support this strategy, the programmer must extend the procotol model with new state reflecting the
intermediate state of incompletely-executed operations; a "stack frame" recording the knowledge
already acquired observing entries and taking conditional branches.
In the distributed setting, the transitions enforce hand-over-hand locking by disallowing
transfer of an entry needed to support an outstanding "stack frame". (Alternatively,
one could allow the transfer but cancel the stack frame, forcing the operation to abort and restart.)
Note that, because the stack frame is explicitly captured, there's no reason
the implementation couldn't transfer the stack frame of an in-progress query
along with the associated state from one host to another, so that a query
begins on one host and is completed on another.

In the shared-memory setting, the developer records each stack frame as a token associated with the entries its
"hands" are holding. 
To make progress on an operation, the sharded state machine requires a thread hold the tokens both for the relevant entries
and the associated stack frame information.
Conversely, the sharded state machine admits no other transitions involving the associated entries:
For an operation to advance to entry j, it must hold the token for that entry, and the token for the stack-frame
info associated with the entry, and (critically) the stack-frame token must be empty.

Note that, just like in the distributed setting, nothing about this protocol state machine prevents the
implementation from passing an in-progress operation off from one thread to another. Because the stack frames
must be accurately accounted for to show the protocol correct, the refining implementation is free to implement those
frames any way it likes. Of course, the most natural implementation is actual stack frames, which remain bound to
a single thread.

In both settings, nothing prevents an implementation from interleaving multiple operations on a single
host or thread. A host (thread) could begin implementing two operations interleaved (perhaps in an event-driven style),
sharing acquired (locked) state between them. Just as with spreading an operation across multiple hosts (threads),
the refinement proof doesn't care which compute unit does the computation, just that the computation reflects the
requirements of the protocol state machine.

# Thrilling conclusion

The fascinating conclusion of this exercise is that one can reason about concurrency over
mutex-protected shared memory using tools isomorphic to reasoning about a distributed shared-nothing
(message-passing) protocol.
In either case, the developer makes an explicit decision about how much concurrency they
wish to support, write a protocol-level state machine model that implements a locking strategy suitable for
that degree of concurrency, and prove that the state machine refines the application spec.

In the distributed setting, the developer designs their own state transfer message protocol; state "ownership"
is a concept constructed entirely in the (verified) protocol state machine.
In the shared-memory setting, the (trusted) infrastructure supplies the mutex mechanism which governs state
ownership and transfer; in exchange, the developer is obliged to express their protocol state machine as a sharded
state machine (monoid resource algebra). In our so-far limited experience, this isn't a great burden in practice,
since the basic strategy even in the distributed case is to decide how to shard system state.

On the implementation side, the systems look very similar: by the time we're operating below the protocol level,
we're no longer concerned about concurrency, just implementing a single transition of that state machine in a thread
or handler.
Each setting incurs obligations that justify the validity of fine-grained reordering.
In the distributed setting, the (trusted) infrastructure demands that each handler complete receiving messages
before it begins sending messages, to justify a reduction (reordering) argument. (A "handler" is a computation
that maintains internal state, such as local variables or conditional branch results.)
The implementation provides an interpretation function from its physical state to the protocol state which
supports that each handler effects some transition of the protocol machine.

In the concurrent setting, the implemetation uses a trusted mutex implementation to guard access to the ghost
tokens that represent shards of the protocol state machine. The implementation code, of course, also guards
access to physical state with the same mutexes; it provides an invariant showing that the physical state and
the ghost tokens are synchronized when released into the mutex. The implementation also uses a trusted "update()"
method to transform a bag of tokens according to the protocol state machine; this obligation is the equivalent
of showing that a handler implements a protocol transition.
