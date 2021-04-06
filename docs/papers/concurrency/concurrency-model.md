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

The protocol layer consisted of a (trusted) distributed system spec that
composed the (trusted) network model with *n* copies of the (verified) program
model, called the Host state machine.  Each Host was an atomic state
machine implementing the protocol above: the program state consisted of an
"ownership table" of which buckets (key ranges) are managed at this host, plus
the key-value pairs known to exist in those buckets. Actions (transitions)
included the sending and receipt of bucket transfer messages and the execution
of user operations, conditioned on the Host having ownership over the buckets
covered by each operation.

### Implementation refinement

The imperative code was a straightforward implementation of the protocol layer
with a correspondingly straightforward refinement proof obligation.
A (trusted) main function called a (verified) initialization routine and then,
in an infinite loop, called a (verified) handler. The handler code
provided an interpretation function that mapped its local state to a Host state.
Each invocation of the handler is shown (via Hoare logic) to transform its
local state in a way such that the interpretations of the before- and after-states
are valid transitions of the protocol Host state machine.

The (verified) main loop controlled access to the network so as to enforce an
ordering condition required to support the (paper-and-pencil) reduction argument that
concurrent execution of handlers on multiple hosts was equivalent to sequenced
execution, so that modeling the handlers as "atomic" steps in the protocol layer
was valid.

### Protocol refinement

This imperative-to-protocol strategy was straightforward in that it would work the
same way with any distribution (concurrency) scheme. The interesting concurrency
reasoning happened in the upper refinement, from the protocol layer to the application
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

The protocol conditions a user operation on local ownership of a bucket, making
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
of the protocol model refine to valid transitions of the application spec.

From the bottom, the imperative handler is shown to manipulate mutexes and the data
behind them in a way that refines to some subset ("shard") of the protocol model.

A (trusted) mutex implementation and a linear type system enforces that protected
data are only accessible by one thread at a time; lock acquisition brings a mutex-protected
datum "into" a thread's shard, corresponding to message delivery in the IronFleet.

The mutex implementation furthermore enforces a (verified) application-specified invariant.
This invariant enables the implementation to relate the physical contents of a mutex to
a ghost shard of the protocol sharded state machine. A thread uses this invariant to demonstrate
that its answers to application requests are consistent with those required by the protocol
state machine (and hence the application spec itself). The mutex spec demands that
threads releasing a mutex establish the invariant so that threads acquiring the mutex
can rely on it.

Note that, while a thread is holding a mutex, it can scramble the physical memory protected
by the mutex however it likes. The mutex contract only requires that, when released, the
physical memory is connected to its ghost representation as specified in the invariant.
This decoupling enables the protocol layer to reason only about the ghost shards, which
effectively only change at each mutex release, and therefore ignore the fine-grained interleavings
of the physical thread states. The intuition for why this decoupling is sound is analogous to the
reduction argument in IronFleet: other threads can only observe this thread through lock release
and acquisition (transfer message send and receipt). If that communication channel is appropriately
constrained, a thread's local behavior is irrelevant so long as it (a) obeys the protocol
when interacting with other threads (sending transfer messages), and (b) obeys the protocol
when revealing values to the user.


