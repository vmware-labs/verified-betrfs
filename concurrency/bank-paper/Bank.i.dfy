include "../framework/AsyncSSM.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Base/Option.s.dfy"
include "../framework/Rw.i.dfy"
include "../../lib/Base/Maps.i.dfy"

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

  lemma sum_delta(numbers: seq<nat>, numbers': seq<nat>, i: nat, delta: int)
  requires |numbers| == |numbers'|
  requires 0 <= i < |numbers|
  requires numbers[i] + delta == numbers'[i]
  requires forall k | 0 <= k < |numbers| && k != i
        :: numbers[k] == numbers'[k]
  ensures sum(numbers') == sum(numbers) + delta
  {
    if i == |numbers| - 1 {
        assert numbers[.. |numbers| - 1] == numbers'[.. |numbers| - 1];
    } else {
        sum_delta(
          numbers[.. |numbers| - 1],
          numbers'[.. |numbers| - 1],
          i,
          delta);
    }
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
    var mid := numbers[i := numbers'[i]];
    sum_delta(numbers, mid, i, mid[i] as int - numbers[i] as int);
    sum_delta(mid, numbers', j, numbers'[j]  as int - mid[j] as int);
  }

  lemma sum_for_init(m: map<nat, nat>, l: nat)
  requires l >= 1
  requires 0 in m
  requires forall i | 1 <= i < l :: i in m && m[i] == 0
  ensures sum(seq(l, (i) requires 0 <= i < l => m[i])) == m[0]
  {
    var t := seq(l, (i) requires 0 <= i < l => m[i]);
    var t0 := seq(l - 1, (i) requires 0 <= i < l - 1 => m[i]);
    assert t[.. |t| - 1] == t0;

    if l == 1 {
      assume sum(t0) == 0;
      assert t[0] == m[0];
      assume sum(t) == sum(t0) + t[0];
      assert sum(t) == m[0];
    } else {
      sum_for_init(m, l-1);
      assert sum(t) == m[0];
    }
  }
}

module Bank refines Rw {
  import MathUtils

  const NumberOfAccounts := 7;

  const FixedTotalMoney := 300;

  /*
   * Declare the type of a 'shard' of the state machine
   * representing our bank application.
   */

  type AccountId = nat
  type Money = nat

  datatype M =
    | M(account_balances: map<AccountId, Money>)
    | Invalid

  predicate valid_shard(a: M) {
    a != Invalid
  }

  /*
   * Define what it means to 'dot' two shard together.
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

  function dot(x: M, y: M) : M
  {
    if x == Invalid || y == Invalid then
      Invalid
    else if maps_overlap(x.account_balances, y.account_balances) then
      Invalid
    else
      M(union_maps(x.account_balances, y.account_balances))
  }

  function I(x: M) : Option<StoredType> {
    None
  }

  /*
   * The 'dot' operation must respect monoidal laws.
   */

  lemma commutative(x: M, y: M)
  ensures dot(x, y) == dot(y, x)
  {
    if dot(x, y) == Invalid {
      assert dot(x, y) == dot(y, x);
    } else {
      assert dot(x, y) == dot(y, x);
    }
  }

  lemma associative(x: M, y: M, z: M)
  ensures dot(dot(x, y), z) == dot(x, dot(y, z))
  {
    if dot(dot(x, y), z) == Invalid {
      assert dot(dot(x, y), z) == dot(x, dot(y, z));
    } else {
      assert dot(dot(x, y), z) == dot(x, dot(y, z));
    }
  }

  function unit() : M {
      M(map[])
  }

  lemma dot_unit(x: M)
  ensures dot(x, unit()) == x
  {
  }

  lemma inv_unit()
  ensures Inv(unit())
  ensures I(unit()) == None
  {
  }

  predicate Init(s: M) {
    && s != Invalid
    && ShardHasAllAccounts(s.account_balances)
    && MathUtils.sum(MapToSeq(s.account_balances)) == FixedTotalMoney
  }

  lemma InitImpliesInv(x: M)
    requires Init(x)
    ensures Inv(x)
  {
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

  predicate Inv(x: M)
  {
    && x != unit() ==> 
        && x != Invalid
        && ShardHasAllAccounts(x.account_balances)
        && MathUtils.sum(MapToSeq(x.account_balances)) == FixedTotalMoney
  }

  /*
   * Our one allowed operation will be to transfer money
   * from one account to another.
   */

  datatype AccountTransfer = AccountTransfer(
      source_account: nat,
      dest_account: nat,
      money: nat)

  predicate Transfer(shard: M, shard': M, transfer: AccountTransfer)
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
    && shard' == M(
      shard.account_balances
        [transfer.source_account := shard.account_balances[transfer.source_account] - transfer.money]
        [transfer.dest_account   := shard.account_balances[transfer.dest_account] + transfer.money]
      )
  }

  lemma Transfer_is_transition(m: M, m': M, transfer: AccountTransfer)
  requires Transfer(m, m', transfer)
  ensures transition(m, m')
  {
    var a := m;
    var b := m';
    forall p: M | Inv(dot(a, p))
    ensures
        && Inv(dot(b, p))
        && I(dot(a, p)) == I(dot(b, p))
    {
        var x := dot(a, p);
        var y := dot(b, p);
        TransferPreservesInv(x, y, transfer);
    }
  }

  /*
   * Show that the operation preserves the state machine invariant.
   */

  lemma TransferPreservesInv(s: M, s': M, transfer: AccountTransfer)
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
