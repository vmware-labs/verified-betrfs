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

  /*
   * Honestly, I don't know much about banking.
   * I doubt I'll get more than 7 customers.
   */
  const NumberOfAccounts := 7;

  const FixedTotalMoney := 300;

  /*
   * Declare the state variable for the state machine
   * representing our bank application.
   */
  datatype Variables = Variables(account_balances: seq<nat>)

  /*
   * Declare our target invariant.
   */
  predicate Inv(s: Variables)
  {
    && |s.account_balances| == NumberOfAccounts    
    && MathUtils.sum(s.account_balances) == FixedTotalMoney
  }

  /*
   * Our one allowed operation will be to transfer money
   * from one account to another.
   */

  datatype AccountTransfer = AccountTransfer(
      source_account: nat,
      dest_account: nat,
      money: nat)

  predicate Transfer(s: Variables, s': Variables, transfer: AccountTransfer)
  {
    // Check that the source account and destination account aren't the same,
    // check that account numbers are valid
    && transfer.source_account != transfer.dest_account
    && 0 <= transfer.source_account < |s.account_balances|
    && 0 <= transfer.dest_account < |s.account_balances|

    // Make sure the source account has enough money to cover the transaction.
    && transfer.money <= s.account_balances[transfer.source_account]

    // Simple balance transfer
    && s' == Variables(
      s.account_balances
        [transfer.source_account := s.account_balances[transfer.source_account] - transfer.money]
        [transfer.dest_account   := s.account_balances[transfer.dest_account] + transfer.money]
      )
  }

  /*
   * Show that the operation preserves the state machine invariant.
   */

  lemma TransferPreservesInv(s: Variables, s': Variables, transfer: AccountTransfer)
  requires Inv(s)
  requires Transfer(s, s', transfer)
  ensures Inv(s')
  {
    // Show that the total amount of money is preserved when we subtract some
    // amount from one balance and add it to another balance.

    MathUtils.sum_is_preserved_on_transfer(
        s.account_balances, s'.account_balances,
        transfer.source_account, transfer.dest_account);
  }
}
