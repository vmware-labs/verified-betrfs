
In order to support a fine-grained locking strategy, we need something other than the monolithic state machine from the previous page.

Thus we will define a sharded state machine, a state machine with an explicit notion of being able to split it into pieces.

For example, in our bank application, we can imagine that the array of accounts could be broken into shards, with different accounts in different shards.

[images/bank_sharded_state.png](images/bank_sharded_state.png)

(Note that the “shards” don’t have to be contiguous in the sense of the array structure—the sequential nature of the array is unimportant. For example, one of the shards in the picture above has accounts 4 and 7.)

When we define state transitions on this state machine, we will define the transitions on the shards. For example, consider the ‘transfer’ operation: it only needs access to two of the accounts to perform its operation. Therefore, we can define the operation on a shard with only 2 accounts in it:

[images/bank_sharded_transition.png](images/bank_sharded_transition.png)

Defining transitions on shards gives rise to a state machine on the “complete” state:

[images/bank_simple_state_machine.png](images/bank_simple_state_machine.png)

This is essentially the same state machine we saw on the last page, and we can use all of our usual tricks to deal with this state machine.

In order to construct a sharded state machine for the bank application, we need to first formalize the notion of ‘sharding.’ The main feature of a sharded state machine is the compositional structure, i.e., given two (or more) shards, we should be able to “glue” them together into a bigger shard. This enables the state machine to have a notion both of the small shards and of the complete state.

It turns out the general algebraic structure for a sharded state machine is a Partial Commutative Monoid (PCM). (https://en.wikipedia.org/wiki/Monoid) PCMs have been known to be useful in concurrent verification for a while. Formally, a PCM is:

- A set M, with a binary operator x · y (the “gluing operation”)
    - · is commutative (i.e., x · y = y · x)
    - · is associative (i.e., (x · y) · z = x · (y · z))
    - · may be partial (x · y may be undefined)

Why do we want these properties?

- Associativity & commutativity: when we “glue” two shards together, it should be symmetric; there’s no sense in which one comes before the other. (Analogy: say you have a jigsaw puzzle. No matter which order you snap the pieces together, you’ll get the same picture in the end.)
- Partiality: it’s possible to have two shards that are incompatible with each other. In this case, composing them simply gives ‘undefined,’ often written bottom (⊥). For example, in the bank application, suppose we had two different shards that both claimed to have ‘account 0’. It would be impossible to compose them. (That’s not to say it’s never possible to have a situation where two monoids “overlap” somehow, but in the bank application, at least, a shard represents exclusive access to the accounts it contains.)

Let’s be a little more concrete.
