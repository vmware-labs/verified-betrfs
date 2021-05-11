module ShardedStateMachine {
  /*
   * A ShardedStateMachine contains a 'Shard' type that represents
   * a shard of the state machine.
   */

  type Shard

  predicate valid_shard(a: Shard)

  /*
   * There must be some notion that lets us put two shards together.
   */

  function glue(a: Shard, b: Shard) : Shard

  /*
   * The 'glue' operation must respect monoidal laws.
   */

  lemma glue_commutative(a: Shard, b: Shard)
  ensures glue(a, b) == glue(b, a)

  lemma glue_associative(a: Shard, b: Shard, c: Shard)
  ensures glue(glue(a, b), c) == glue(a, glue(b, c))

  function unit() : Shard
  ensures valid_shard(unit())

  lemma glue_unit(a: Shard)
  ensures glue(a, unit()) == a

  /*
   * The invariant is meant to hold on a 'whole' shard,
   * that is, all the pieces glued together at once.
   */

  predicate Inv(s: Shard)

  /*
   * 'Next' predicate of our state machine.
   */

  predicate Next(shard: Shard, shard': Shard)

  lemma NextPreservesValid(s: Shard, s': Shard)
  requires valid_shard(s)
  requires Next(s, s')
  ensures valid_shard(s')

  lemma NextAdditive(s: Shard, s': Shard, t: Shard)
  requires Next(s, s')
  requires valid_shard(glue(s, t))
  requires Next(glue(s, t), glue(s', t))

  /*
   * Show that the operation preserves the state machine invariant.
   */

  lemma TransferPreservesInv(s: Shard, s': Shard, transfer: AccountTransfer)
  requires Inv(s)
  requires Transfer(s, s', transfer)
  ensures Inv(s')
  {
    // Show that the total amount of money is preserved when we subtract some
    // amount from one balance and add it to another balance.

    MathUtils.sum_is_preserved_on_transfer(
        MapToSeq(s.account_balances),
        MapToSeq(s'.account_balances),
        transfer.source_account, transfer.dest_account);
  }
}
