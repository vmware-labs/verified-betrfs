# Linearizability of NRSimple

In NRSimple.i.dfy, an update _U_ has the following life cycle:

 1. Append the operation _U.op_ at some index _U.idx_
 2. Return at some point when _ctail >= U.idx_

A readonly op _R_ has the following life cycle:

 1. Write down _ctail_ value as _R.baseCtail_
 2. Return the result at some version _R.v_ where _R.baseCtail <= R.v <= ctail_
    (i.e., _R.v_ is between the original _ctail_ value it observed and the _ctail_ value at the time of the response).

Furthermore, the _ctail_ value is allowed to nondeterministially increase at any point in time.

The linearizability argument goes:

 * An update _U_ can put its linearization point at the point in time when _ctail_ equals _U.idx_.
   This will always happen before the update returns, because we require that _ctail >= U.idx_.
 * A readonly operation _R_ can put its linearization point at the point in time when _ctail_ equals _U.idx_
   (right after the linearization point for the corresponding update). Of course, this will always be
   between the start and end of the request, because of the requirement that _R.baseCtail <= R.v <= ctail_.

# On having InfiniteLog refine NRSimple

 * We have _ctail >= U.idx_ because an update will not complete until the `exec` call completes, which increases the `ctail`.
 * We have _R.v >= R.baseCtail_ because a read operation observes the ctail, then waits until the localTail is >= that value.
 * We have _R.v <= ctail_ because when a thread performs a read, the version it reads must be <= the ctail.

Note that the bug we idenfitifed earlier is crucial for the third point. The algorithm now requires the node's lock to be held exclusively while `exec` runs.
Therefore, even though the node's replica potentially gets ahead of the _ctail_ during the `exec` call, the read cannot occur during this time.

In terms of the state machine, this means that a read requires us to be in the `CombinerIdle` state.
