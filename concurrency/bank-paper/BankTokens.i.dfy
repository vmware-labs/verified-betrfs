include "Bank.i.dfy"
include "../framework/GlinearMap.s.dfy"
include "../framework/Ptrs.s.dfy"

module BankTokens {
  import Bank
  import GlinearMap
  import opened Options
  import opened GhostLoc
  import opened NativeTypes
  import opened RequestIds
  import BankTokens = RwTokens(Bank)
  import MathUtils
  import Ptrs

  datatype {:glinear_fold} Account = Account(ghost loc_s: nat, ghost id: nat, ghost balance: nat)
  {
    function defn(): BankTokens.Token {
      BankTokens.T.Token(
          ExtLoc(loc_s, BankTokens.Wrap.singleton_loc()),
          Bank.M(map[id := balance]))
    }
  }

  glinear method do_transfer(glinear acct1: Account, glinear acct2: Account, ghost bal: nat)
  returns (glinear acct1': Account, glinear acct2': Account)
  requires acct1.id != acct2.id
  requires acct1.loc_s == acct2.loc_s
  requires bal <= acct1.balance
  requires 0 <= acct1.id < Bank.NumberOfAccounts
  requires 0 <= acct2.id < Bank.NumberOfAccounts

  ensures acct1' == Account(acct1.loc_s, acct1.id, acct1.balance - bal)
  ensures acct2' == Account(acct2.loc_s, acct2.id, acct2.balance + bal)
  {
    glinear var a_token := Account_unfold(acct1);
    glinear var b_token := Account_unfold(acct2);

    ghost var out_expect_a := Account(acct1.loc_s, acct1.id, acct1.balance - bal);
    ghost var out_token_expect_a := Account_unfold(out_expect_a);

    ghost var out_expect_b := Account(acct2.loc_s, acct2.id, acct2.balance + bal);
    ghost var out_token_expect_b := Account_unfold(out_expect_b);

    Bank.Transfer_is_transition(
      Bank.dot(a_token.val, b_token.val),
      Bank.dot(out_token_expect_a.val, out_token_expect_b.val),
      Bank.AccountTransfer(acct1.id, acct2.id, bal)
    );

    glinear var out_token_a, out_token_b := BankTokens.internal_transition_2_2(
      a_token, b_token, out_token_expect_a.val, out_token_expect_b.val
    );

    acct1' := Account_fold(out_expect_a, out_token_a);
    acct2' := Account_fold(out_expect_b, out_token_b);
  }

  glinear method do_init_accounts(glinear t: BankTokens.Token)
  returns (glinear accounts: map<nat, Account>)
  requires (
    t.val.M? &&
    (forall x : nat | 0 <= x < Bank.NumberOfAccounts :: x in t.val.account_balances)
  )
  ensures forall x | 0 <= x < Bank.NumberOfAccounts ::
    x in accounts && accounts[x] == Account(t.loc.s, x, t.val.account_balances[x])
  {
    glinear var t' := t;
    ghost var j := 0;
    accounts := GlinearMap.glmap_empty();

    while j < Bank.NumberOfAccounts
    invariant 0 <= j <= Bank.NumberOfAccounts
    invariant t'.loc == t.loc
    invariant t'.val.M?
    invariant forall i | 0 <= i < j :: i in accounts && accounts[i] ==
        Account(t.loc.s, i, t.val.account_balances[i])
    invariant forall i | j <= i <  Bank.NumberOfAccounts ::
        i in t'.val.account_balances && t.val.account_balances[i] == t'.val.account_balances[i]
    {
      var expected := Account(t.loc.s, j, t.val.account_balances[j]);
      var x := expected.defn().val;
      var y := t'.val.(account_balances := t'.val.account_balances - {j});

      glinear var xl;
      t', xl := BankTokens.T.split(t', y, x);

      glinear var z := Account_fold(expected, xl);
      accounts := GlinearMap.glmap_insert(accounts, j, z);
      j := j + 1;
    }

    Ptrs.dispose_anything(t');
  }

  glinear method bank_initialize()
  returns (
    ghost loc_s: nat,
    glinear accounts: map<nat, Account>
  )
  ensures forall i | 0 <= i < Bank.NumberOfAccounts as int ::
      i in accounts && accounts[i] == Account(loc_s, i, if i == 0 then Bank.FixedTotalMoney else 0)
  {
    ghost var new_accounts := map x : nat | 0 <= x < (Bank.NumberOfAccounts as nat) :: (if x == 0 then Bank.FixedTotalMoney else 0);
    ghost var m := Bank.M(new_accounts);

    MathUtils.sum_for_init(new_accounts, Bank.NumberOfAccounts);
    Bank.InitImpliesInv(m);
    glinear var token := BankTokens.initialize_empty(m);

    accounts := do_init_accounts(token);
    loc_s := token.loc.s;
  }

  glinear method get_bound(gshared acct1: Account)
  requires 0 <= acct1.id < Bank.NumberOfAccounts
  ensures acct1.balance <= Bank.FixedTotalMoney
  {
    gshared var a_token := Account_unfold_borrow(acct1);
    ghost var rest := BankTokens.obtain_invariant_1(a_token);
    ghost var x := Bank.dot(a_token.val, rest);
    assert x != Bank.unit() by {
      assert acct1.id in x.account_balances;
      assert acct1.id !in Bank.unit().account_balances;
    }
    //assert Bank.Inv(x);
    //assert Bank.ShardHasAllAccounts(x.account_balances);
    MathUtils.sum_ge(
      Bank.MapToSeq(x.account_balances),
      acct1.id);
  }
}
