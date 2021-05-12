include "Bank_ShardedStateMachine.dfy"
include "LinearMutex.dfy"

module SSMTokens {
  import Bank

  // Every token corresponds to some "shard" of the state machine.
  // The tokens are not "real" (i.e., they don't appear in a compiled binary).
  // They are 'ghost linear' (glinear).
  type {:extern} Token {
    function value() : Bank.Shard
  }

  /*
   * Given 2 tokens, glue their shards together according to the monoidal structure
   * defined by the bank SSM, thus returning just a single token.
   */
  glinear method glue(glinear a: Token, glinear b: Token)
  returns (glinear c: Token)
  ensures c.value() == Bank.glue(a.value(), b.value())

  /*
   * Do the opposite - split a token into two.
   * The split_1 and split_2 arguments allow the caller to specify how they
   * want the token to be split.
   */
  glinear method split(glinear c: Token,
      ghost split_1: Bank.Shard,
      ghost split_2: Bank.Shard)
  returns (glinear a: Token, glinear b: Token)
  requires c.value() == Bank.glue(split_1, split_2)
  ensures a.value() == split_1
  ensures b.value() == split_2

  /*
   * Given a shard, perform a transition as allowed by the SSM.
   * In this case, the allowed transitions are given by the Bank.Transfer predicate.
   */
  glinear method perform_transfer(
      glinear token: Token,
      ghost shard: Bank.Shard,
      ghost shard': Bank.Shard,
      ghost transfer: Bank.AccountTransfer)
  returns (glinear token': Token)
  requires token.value() == shard
  requires Bank.Transfer(shard, shard', transfer)
  ensures token'.value() == shard'

  /*
   * For any token that exists in the program, its shard must be the sub-shard
   * of some whole which meets the SSM's invariant. This "lemma"
   * (expressed as a glinear method) simply says that this is mathematically possible.
   * The parameter is 'gshared' (i.e., calling this method does not consume the token).
   */
  glinear method get_invariant(gshared token: Token)
  ensures exists rest :: Bank.Inv(Bank.glue(token.value(), rest))
}

module AdditionalMathUtils {
  import MathUtils

  lemma lemma_single_elem_le_sum_of_map(i: int, s: seq<nat>)
  requires 0 <= i < |s|
  ensures s[i] <= MathUtils.sum(s)
  {
    if i == |s| - 1 {
      // done
    } else {
      // induction
      lemma_single_elem_le_sum_of_map(i, s[..|s|-1]);
    }
  }
}

module BankImplementation {
  import Bank
  import SSMTokens
  import MathUtils
  import opened LinearMutexes
  import AdditionalMathUtils

  linear datatype AccountEntry = AccountEntry(
      balance: nat,
      glinear token: SSMTokens.Token
    )

  predicate Inv(accountId: nat, entry: AccountEntry) {
    entry.token.value() == Bank.Shard(map[accountId := entry.balance])
  }

  datatype AccountSeq = AccountSeq(accounts: seq<Mutex<AccountEntry>>)
  {
    predicate WellFormed()
    {
      && |this.accounts| == Bank.NumberOfAccounts
      && (forall accountId | 0 <= accountId < Bank.NumberOfAccounts ::
          forall entry ::
            this.accounts[accountId].inv(entry) <==> Inv(accountId, entry)
      )
    }
  }

  /*
   * Do the transfer (but only if the source account has enough money)
   * Return 'true' on success (the return value is not verified in any sense)
   */
  method TryAccountTransfer(
      accountSeq: AccountSeq,
      sourceAccountId: nat,
      destAccountId: nat,
      amount: nat)
  returns (success: bool)
  requires accountSeq.WellFormed()
  requires 0 <= sourceAccountId < Bank.NumberOfAccounts
  requires 0 <= destAccountId < Bank.NumberOfAccounts
  requires sourceAccountId != destAccountId
  {
    var accounts := accountSeq.accounts;

    // 1. Acquire the two mutexes

    linear var sourceAccountEntry, destAccountEntry;
    glinear var handle1, handle2;
    sourceAccountEntry, handle1 := accounts[sourceAccountId].acquire();
    destAccountEntry, handle2 := accounts[destAccountId].acquire();

    // unpack the datatypes to the physical state (sourceBalance and destBalance)
    // and the ghost state (sourceToken and destToken)

    linear var AccountEntry(sourceBalance, sourceToken) := sourceAccountEntry;
    linear var AccountEntry(destBalance, destToken) := destAccountEntry;

    var newSourceBalance: nat;
    var newDestBalance: nat;

    if amount <= sourceBalance {
      // 2. Update the source balance.

      // (We do this all on the stack, but an alternative implementation might have
      // us update a shared memory cell, which we would gain exclusive access to via
      // the mutex.)

      newSourceBalance := sourceBalance - amount;

      // 3. Update the dest balance.

      newDestBalance := destBalance + amount;

      // 4. Ghost update here

      ////////////////////////////
      ////////////////////////////

      // This is the interesting bit, although it's a little bogged down in boilerplate.
      // We have 2 tokens, so we start by gluing them together into a single token
      // which contains both accounts.

      glinear var twoAccountToken := SSMTokens.glue(sourceToken, destToken);

      // Our Bank SSM defines an 'AccountTransfer' transition, which allows a transition
      // on a shard that has 2 accounts in it:

      glinear var twoAccountToken' := SSMTokens.perform_transfer(twoAccountToken,
          Bank.Shard(map[sourceAccountId := sourceBalance, destAccountId := destBalance]),
          Bank.Shard(map[sourceAccountId := newSourceBalance, destAccountId := newDestBalance]),
          Bank.AccountTransfer(sourceAccountId, destAccountId, amount));

      // Now we split our transformed state back into two tokens.

      sourceToken, destToken := SSMTokens.split(twoAccountToken',
          Bank.Shard(map[sourceAccountId := newSourceBalance]),
          Bank.Shard(map[destAccountId := newDestBalance]));

      ////////////////////////////
      ////////////////////////////

      success := true;
    } else {
      newSourceBalance := sourceBalance;
      newDestBalance := destBalance;

      success := false;
    }

    // 5. Release the locks

    accounts[sourceAccountId].release(AccountEntry(newSourceBalance, sourceToken), handle1);
    accounts[destAccountId].release(AccountEntry(newDestBalance, destToken), handle2);
  }

  method AssertAccountIsNotTooRich(
      accountSeq: AccountSeq,
      accountId: nat)
  requires accountSeq.WellFormed()
  requires 0 <= accountId < Bank.NumberOfAccounts
  {
    var accounts := accountSeq.accounts;

    linear var accountEntry;
    glinear var handle;
    accountEntry, handle := accounts[accountId].acquire();

    linear var AccountEntry(balance, token) := accountEntry;

    SSMTokens.get_invariant(token);

    // This assertion doesn't follow from the invariant of a single mutex!
    // But we can derive it from the global protocol governing the bank accounts.
    assert balance <= 300 by {
      // Here's how. (Most of the assertions here aren't necessary, and only serve
      // as documentation.)

      // We've got a token (corresponding to a shard totally just the 1 bank account).
      // The above call (get_invariant) lets us learn that this shard must be a subcomponent
      // of a large _complete_ state that satisfies the invariant proved in the
      // Bank_ShardedStateMachine. Let's obtain that shard, call it 'full'.
      ghost var rest :| Bank.Inv(Bank.glue(token.value(), rest));
      ghost var full := Bank.glue(token.value(), rest);
      assert Bank.Inv(full);

      // It's worth keeping in mind that 'full' here isn't a token. We haven't magically
      // obtained all the tokens in the system, or pulled them out of the mutexes.
      // It's just a mathematical construct that we obtained from an existential first-order
      // logic formula.

      // Anyway, since the 'full' shard contains the 'token.value()' shard as a
      // sub-component, it should have the accountId -> balance mapping in it.

      assert balance == full.account_balances[accountId];

      // The single balance is <= the sum of all balances. This is just a math lemma.

      AdditionalMathUtils.lemma_single_elem_le_sum_of_map(
          accountId,
          Bank.MapToSeq(full.account_balances));
      assert full.account_balances[accountId]
          <= MathUtils.sum(Bank.MapToSeq(full.account_balances));

      // Now, the sum of all balances is Bank.FixedTotalMoney.
      // We get this from Bank.Inv(full).

      assert MathUtils.sum(Bank.MapToSeq(full.account_balances)) == Bank.FixedTotalMoney;

      // And this constant was defined to be 300:

      assert Bank.FixedTotalMoney == 300;

      // So in the end we derive:

      assert balance <= 300;
    }

    accounts[accountId].release(AccountEntry(balance, token), handle);
  }
}
