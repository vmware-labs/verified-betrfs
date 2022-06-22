include "BankTokens.i.dfy"
include "../framework/Mutex.i.dfy"
include "../../lib/Lang/LinearSequence.i.dfy"

module BankSpec {
  import opened NativeTypes
  type AccountSeq

  predicate WF(a: AccountSeq)

  method AssertAccountIsNotTooRich(
      shared accountSeq: AccountSeq,
      accountId: uint64)
  returns (bal: int)
  requires WF(accountSeq)
  requires 0 <= accountId as int < 7
  ensures bal <= 300
  decreases *

  method TryAccountTransfer(
      shared accountSeq: AccountSeq,
      sourceAccountId: uint64,
      destAccountId: uint64,
      amount: nat)
  returns (success: bool)
  requires WF(accountSeq)
  requires 0 <= sourceAccountId as int < 7
  requires 0 <= destAccountId as int < 7
  requires sourceAccountId != destAccountId
  decreases *
}
