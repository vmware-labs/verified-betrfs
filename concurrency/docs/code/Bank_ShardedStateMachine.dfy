module MathUtils {
  /*
   * Inductively define the sum of a sequence of integers
   */
  function sum(numbers: seq<nat>) : nat
  {
    if |numbers| == 0 then
      0
    else
      sum(numbers[.. |numbers| - 1]) + numbers[|numbers| - 1]
  }

  /*
   * Utility lemma for showing that sum is preserved when
   * two number of a sequence change.
   */
  lemma sum_is_preserved_on_transfer(numbers: seq<nat>, numbers': seq<nat>, i: nat, j: nat)
  requires |numbers| == |numbers'|
  requires 0 <= i < |numbers|
  requires 0 <= j < |numbers|
  requires i != j
  requires numbers[i] + numbers[j] == numbers'[i] + numbers'[j]
  requires forall k | 0 <= k < |numbers| && k != i && k != j
        :: numbers[k] == numbers'[k]
  ensures sum(numbers) == sum(numbers')
  {
    // excercise: fill in the proof
  }
}

module Bank {
  import MathUtils

  const NumberOfAccounts := 7;

  const FixedTotalMoney := 300;

  /*
   * Declare the type of a 'shard' of the state machine
   * representing our bank application.
   */

  type AccountId = nat
  type Money = nat

  datatype Shard =
    | Shard(account_balances: map<AccountId, Money>)
    | Invalid

  predicate valid_shard(a: Shard) {
    a != Invalid
  }

  /*
   * Define what it means to 'glue' two shard together.
   *
   * In this case, a 'shard' is essentially a subset of the
   * accounts. So gluing two shards together means taking the union.
   *
   * If the two shards overlap, the result is undefined.
   */

  predicate maps_overlap(a: map<AccountId, Money>, b: map<AccountId, Money>)
  {
    exists account_id :: account_id in a && account_id in b
  }

  function union_maps(a: map<AccountId, Money>, b: map<AccountId, Money>) : map<AccountId, Money>
  {
    map account_id | account_id in (a.Keys + b.Keys)
      :: (if account_id in a.Keys then a[account_id] else b[account_id])
  }

  function glue(a: Shard, b: Shard) : Shard
  {
    if a == Invalid || b == Invalid then
      Invalid
    else if maps_overlap(a.account_balances, b.account_balances) then
      Invalid
    else
      Shard(union_maps(a.account_balances, b.account_balances))
  }

  /*
   * The 'glue' operation must respect monoidal laws.
   */

  lemma glue_commutative(a: Shard, b: Shard)
  ensures glue(a, b) == glue(b, a)
  {
    if glue(a, b) != Invalid {
      var x := glue(a, b).account_balances;
      var y := glue(b, a).account_balances;
      assert x == y by {
        assert forall id | id in x :: x[id] == y[id];
      }
    }
  }

  lemma glue_associative(a: Shard, b: Shard, c: Shard)
  ensures glue(glue(a, b), c) == glue(a, glue(b, c))
  {
    if glue(glue(a, b), c) != Invalid {
      var x := glue(glue(a, b), c).account_balances;
      var y := glue(a, glue(b, c)).account_balances;
      assert x == y by {
        assert forall id | id in x :: x[id] == y[id];
      }
    }
  }

  /*
   * Declare our target invariant.
   * The invariant is meant to hold on a 'whole' shard,
   * that is, all the pieces glued together at once.
   */

  predicate ShardHasAllAccounts(accounts: map<AccountId, Money>)
  {
    forall i | 0 <= i < NumberOfAccounts :: i in accounts
  }

  function MapToSeq(accounts: map<AccountId, Money>) : seq<nat>
  requires ShardHasAllAccounts(accounts)
  {
    seq(NumberOfAccounts, (i) requires 0 <= i < NumberOfAccounts => accounts[i])
  }

  predicate Inv(s: Shard)
  {
    && s != Invalid
    && ShardHasAllAccounts(s.account_balances)
    && MathUtils.sum(MapToSeq(s.account_balances)) == FixedTotalMoney
  }

  /*
   * Our one allowed operation will be to transfer money
   * from one account to another.
   */

  datatype AccountTransfer = AccountTransfer(
      source_account: nat,
      dest_account: nat,
      money: nat)

  predicate Transfer(shard: Shard, shard': Shard, transfer: AccountTransfer)
  {
    // Naturally, we won't allow an operation on invalid states.
    && shard != Invalid
    && shard' != Invalid

    // Check that the source account and destination account aren't the same,
    // check that account numbers are valid
    && transfer.source_account != transfer.dest_account
    && 0 <= transfer.source_account < NumberOfAccounts
    && 0 <= transfer.dest_account < NumberOfAccounts

    // Check that the shard we're operating on actually has the two accounts
    // we care about. (It could have more as well, those don't matter, but we
    // definitely need these two.)
    && transfer.source_account in shard.account_balances
    && transfer.dest_account in shard.account_balances

    // Make sure the source account has enough money to cover the transaction.
    && transfer.money <= shard.account_balances[transfer.source_account]

    // Simple balance transfer
    && shard' == Shard(
      shard.account_balances
        [transfer.source_account := shard.account_balances[transfer.source_account] - transfer.money]
        [transfer.dest_account   := shard.account_balances[transfer.dest_account] + transfer.money]
      )
  }

  lemma TransferPreservesValid(s: Shard, s': Shard, transfer: AccountTransfer)
  requires valid_shard(s)
  requires Transfer(s, s', transfer)
  ensures valid_shard(s')
  {
  }

  lemma TransferAdditive(s: Shard, s': Shard, transfer: AccountTransfer, t: Shard)
  requires Transfer(s, s', transfer)
  requires valid_shard(glue(s, t))
  requires Transfer(glue(s, t), glue(s', t), transfer)
  {
  }

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
