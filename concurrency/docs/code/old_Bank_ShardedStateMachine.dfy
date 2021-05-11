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

module Options {
  datatype Option<V> = None | Some(value:V)
}

module Bank {
  import MathUtils
  import opened Options

  const NumberOfAccounts := 7;

  const FixedTotalMoney := 300;

  /*
   * Declare the type of a 'shard' of the state machine
   * representing our bank application.
   */

  type FixedLengthSeq = s : seq<Option<nat>> | (|s| == NumberOfAccounts)
    witness *

  datatype Shard =
    | Shard(account_balances: FixedLengthSeq)
    | Invalid

  predicate valid_shard(a: Shard) {
    a != Invalid
  }

  /*
   * Define what it means to 'glue' two shard together.
   *
   * In this case, a 'shard' is essentially a subset of the
   * array representing the accounts. So gluing two shards
   * together means taking the union.
   *
   * If the two shards overlap, the result is undefined.
   */

  predicate sequences_overlap(a: seq<Option<nat>>, b: seq<Option<nat>>)
  requires |a| == |b|
  {
    exists i :: 0 <= i < |a| && a[i].Some? && b[i].Some?
  }

  function merge_sequences(a: seq<Option<nat>>, b: seq<Option<nat>>) : seq<Option<nat>>
  requires |a| == |b|
  {
    seq(|a|, (i) requires 0 <= i < |a| =>
      (if a[i].Some? then a[i]
       else if b[i].Some? then b[i]
       else None
      )
    )
  }

  function glue(a: Shard, b: Shard) : Shard
  {
    if a == Invalid || b == Invalid then
      Invalid
    else if sequences_overlap(a.account_balances, b.account_balances) then
      Invalid
    else
      Shard(merge_sequences(a.account_balances, b.account_balances))
  }

  method glue_commutative(a: Shard, b: Shard)
  ensures glue(a, b) == glue(b, a)
  {
    if a == Invalid || b == Invalid {
      calc {
        glue(a, b);
        Invalid;
        glue(b, a);
      }
    } else if sequences_overlap(a.account_balances, b.account_balances) {
      calc {
        glue(a, b);
        Invalid;
        glue(b, a);
      }
    } else {
      var x := glue(a, b).account_balances;
      var y := glue(b, a).account_balances;
      assert x == y by {
        assert forall i | 0 <= i < |x| :: x[i] == y[i];
      }
    }
  }

  method glue_associative(a: Shard, b: Shard, c: Shard)
  ensures glue(glue(a, b), c) == glue(a, glue(b, c))
  {
    if glue(glue(a, b), c) != Invalid {
      var x := glue(glue(a, b), c).account_balances;
      var y := glue(a, glue(b, c)).account_balances;
      assert x == y by {
        assert forall i | 0 <= i < |x| :: x[i] == y[i];
      }
    }
  }

  /*
   * Declare our target invariant.
   */

  predicate Complete(s: seq<Option<nat>>)
  {
    forall i | 0 <= i < |s| :: s[i].Some?
  }

  function RemoveOptions(s: seq<Option<nat>>) : seq<nat>
  requires Complete(s)
  {
    seq(|s|, (i) requires 0 <= i < |s| => s[i].value)
  }

  predicate Inv(s: Shard)
  {
    && s != Invalid
    && |s.account_balances| == NumberOfAccounts    
    && Complete(s.account_balances)
    && MathUtils.sum(RemoveOptions(s.account_balances)) == FixedTotalMoney
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
    && shard != Invalid
    && shard' != Invalid

    // Check that the source account and destination account aren't the same,
    // check that account numbers are valid
    && transfer.source_account != transfer.dest_account
    && 0 <= transfer.source_account < |shard.account_balances|
    && 0 <= transfer.dest_account < |shard.account_balances|

    && shard.account_balances[transfer.source_account].Some?
    && shard.account_balances[transfer.dest_account].Some?

    // Make sure the source account has enough money to cover the transaction.
    && transfer.money <= shard.account_balances[transfer.source_account].value

    // Simple balance transfer
    && shard' == Shard(
      shard.account_balances
        [transfer.source_account := Some(shard.account_balances[transfer.source_account].value - transfer.money)]
        [transfer.dest_account   := Some(shard.account_balances[transfer.dest_account].value + transfer.money)]
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
        RemoveOptions(s.account_balances),
        RemoveOptions(s'.account_balances),
        transfer.source_account, transfer.dest_account);
  }
}
