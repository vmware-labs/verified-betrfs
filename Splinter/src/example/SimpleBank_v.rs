pub mod spec;
pub mod exec;

use std::sync::Arc;
use std::thread::*;

use builtin::*;
use builtin_macros::*;
use vstd::{map::*, seq::*, rwlock::*, slice::*};
use crate::exec::Bank_v::*;
use crate::spec::BankSpec_t::{Request, Reply, Input, Output, ReqID};

verus!{

struct AccountInfo {
    pub amt: u32, // physical value
    pub acc_token: Tracked<Bank::account_map>, // permission tokens, compiled away
}
    
struct AccountInv {
    pub key: usize,
    pub instance: Bank::Instance,
}
    
impl RwLockPredicate<AccountInfo> for AccountInv {
    open spec fn inv(self, info: AccountInfo) -> bool {
        &&& info.amt == info.acc_token@@.value  // physical value matches the tracked ghost value
        &&& self.key == info.acc_token@@.key    // token corresponds to_id the right key (AccID)
        &&& self.instance == info.acc_token@@.instance // token corresponds to_id the right instance of the protocol
    }
}

struct SimpleBank {
    pub accounts: Vec<RwLock::<AccountInfo, AccountInv>>, // AccID implied by the index
    pub instance: Tracked<Bank::Instance>,
}
    
impl SimpleBank {
    pub closed spec fn wf(self) -> bool
    {
        forall |acc| 0 <= acc < self.accounts.len()
        ==> {
            // requires that account inv is tracking the correct instance and key
            &&& #[trigger] self.accounts[acc].pred().instance == self.instance@
            &&& self.accounts[acc].pred().key == acc
        }
    }

    pub closed spec fn valid_id(self, id: usize) -> bool
    {
        id < self.accounts.len()
    }

    pub fn new(total_accounts: usize, initial_amount: u32) -> (out: Self)
        ensures 
            out.wf(),
            forall |acc: usize| acc < total_accounts ==> out.valid_id(acc)
    {
        let tracked (
            Tracked(instance),
            Tracked(account_map),   // perm map
            Tracked(requests),      // request perm map (multiset)
            Tracked(replies),       // reply perm map (multiset)
            Tracked(id_history),    // tracked id history
        ) = Bank::Instance::initialize(total_accounts as nat, initial_amount as nat);

        let mut accounts = Vec::<RwLock<AccountInfo, AccountInv>>::new();
        while accounts.len() < total_accounts
        invariant
            forall|j: nat| accounts.len() <= j < total_accounts 
            ==> {
                &&& #[trigger] account_map.dom().contains(j)
                &&& account_map[j]@.value == initial_amount as nat
                &&& account_map[j]@.instance == instance
                &&& account_map[j]@.key == j
            },
            forall|j: int| 0 <= j < accounts.len() ==>
            {
                &&& (#[trigger] accounts[j]).pred().instance == instance
                &&& accounts[j].pred().key == j
            }
        {
            let ghost i = accounts.len();
            assert(account_map.dom().contains(i as nat)); // trigger

            let acc = AccountInfo{
                amt: initial_amount, 
                acc_token: Tracked(account_map.tracked_remove(i as nat))
            };
            let inv = Ghost(AccountInv{key: i, instance});    
            let entry = RwLock::<AccountInfo, AccountInv>::new(acc, inv);
            accounts.push(entry);
        }
 
        SimpleBank{
            accounts: accounts,
            instance: Tracked(instance)
        }
    }

    pub fn failed_reply(&self, req: Request, req_shard: Tracked<Bank::requests>)
        -> (out: (Reply, Tracked<Bank::replies>))
        requires 
            self.wf(),
            req_shard@@.instance == self.instance@,
            req_shard@@.key == req,
            req_shard@@.count == 1,
        ensures
            out.1@@.instance == self.instance@,
            out.1@@.key == out.0,
            out.1@@.count == 1,
    {
        let reply = Reply{output: Output{succeeded: false}, id: req.id};
        let Tracked(req_token) = req_shard;
        let tracked replies = self.instance.borrow().failed_transfer(Bank::Label::ExecuteOp{req, reply}, req_token);
        return (reply, Tracked(replies));
    }

    // takes an immutable self due to interior mutability 
    pub fn maybe_transfer(&self, req: Request, req_shard: Tracked<Bank::requests>) 
        -> (out: (Reply, Tracked<Bank::replies>))
        requires 
            self.wf(),
            req_shard@@.instance == self.instance@,
            req_shard@@.key == req,
            req_shard@@.count == 1,
        ensures
            out.1@@.instance == self.instance@,
            out.1@@.key == out.0,
            out.1@@.count == 1,
    {
        let Input{from, to, amt} = req.input;

        if from == to || from >= self.accounts.len() || to >= self.accounts.len() {
            return self.failed_reply(req, req_shard);
        }

        let (
            (from_acc, from_handle),
            (to_acc, to_handle)
        ) =  if from < to {
            (self.accounts[from].acquire_write(), self.accounts[to].acquire_write())
        } else {
            let min = self.accounts[to].acquire_write();
            (self.accounts[from].acquire_write(), min)
        };

        if from_acc.amt >= amt && to_acc.amt <= u32::MAX - amt {
            let AccountInfo{amt: from_amt, acc_token: Tracked(from_token)} = from_acc;
            let AccountInfo{amt: to_amt, acc_token: Tracked(to_token)}= to_acc;
            let Tracked(req_token) = req_shard;
            let reply = Reply{output: Output{succeeded: true}, id: req.id};

            let tracked (
                Tracked(new_from_token),
                Tracked(new_to_token),
                Tracked(new_reply_token),
            ) = self.instance.borrow().transfer(
                Bank::Label::ExecuteOp{req, reply},
                from_token,
                to_token,
                req_token,
            );

            let new_from_acc = AccountInfo{amt: (from_amt - amt) as u32, acc_token: Tracked(new_from_token) };
            let new_to_acc = AccountInfo{amt: (to_amt + amt) as u32, acc_token: Tracked(new_to_token) };
            from_handle.release_write(new_from_acc);
            to_handle.release_write(new_to_acc);
            return (reply, Tracked(new_reply_token));
        } else {
            from_handle.release_write(from_acc);
            to_handle.release_write(to_acc);
            return self.failed_reply(req, req_shard);
        }
    }

    pub fn check_value(&self, id: usize) -> u64
    requires 
        self.wf(),
        self.valid_id(id),
    {
        let handle = self.accounts[id].acquire_read();
        let v = handle.borrow().amt as u64;
        handle.release_read();
        v
    }

    // not thread safe
    pub fn get_total(&self) -> u64
        requires 
            self.wf(),
    {
        let mut i = 0;
        let mut total: u64 = 0;
        while i < self.accounts.len()
        invariant
            i <= self.accounts.len()
        {
            let handle = self.accounts[i].acquire_read();
            let amt = handle.borrow().amt as u64;
            handle.release_read();
            if amt <= u64::MAX - total {
                total += amt;
            } else {
                return total;
            }
            i += 1;
        }
        total
    }

    // workaround cause we can't create this in normal rust
    pub fn get_new_api(&self) -> (out: TrustedAPI)
        ensures self.instance@ == out.instance()
    {
        TrustedAPI::new(Ghost(self.instance@))
    }
}

fn basic_test() {
    let bank = SimpleBank::new(10, 10);
    let api = TrustedAPI::new(Ghost(bank.instance@));
    let (req, req_shard, id_shard) = api.receive_request(true);
    let (reply, reply_shard) = bank.maybe_transfer(req, req_shard);
    api.send_reply(reply, reply_shard, true);
}
}

fn main() {
    basic_test();

    let total_accs = 1000;
    let initial_amt = 15;
    let num_threads = 10;

    let bank = SimpleBank::new(total_accs, initial_amt);
    let api = bank.get_new_api(); // this should be associated with an instance

    let shared_bank = Arc::new(bank);
    let shared_api = Arc::new(api);
    println!("initial total: {}", shared_bank.get_total());

    let mut handles = Vec::new();
    let mut n:usize = 0;

    while n < num_threads {
        let shared_bank = shared_bank.clone();
        let shared_api = shared_api.clone();
        handles.push(spawn(
            move || {
                let print = false;
                let mut failure_count:usize = 0;
                let mut i:usize = 0;
                while i < 100
                {
                    let (req, req_shard, id_shard) = shared_api.receive_request(print);
                    let (reply, reply_shard) = shared_bank.maybe_transfer(req, req_shard);
                    if !reply.output.succeeded {
                        failure_count = failure_count + 1;
                    }
                    shared_api.send_reply(reply, reply_shard, print);
                    i = i + 1;
                }
                println!("thread: {} | failed transfers: {}", n, failure_count);
            },
        ));
        n = n + 1;
    }

    for handle in handles.into_iter() {
        match handle.join() {
            Result::Ok(()) => {}
            _ => {
                return;
            }
        };
    }
    println!("post total: {}", shared_bank.get_total());
}