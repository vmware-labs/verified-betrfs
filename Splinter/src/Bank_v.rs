use std::sync::Arc;
use vstd::atomic_ghost::*;
use vstd::cell::*;
use vstd::map::*;
use vstd::map_lib::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::{pervasive::*, prelude::*, *};
use vstd::rwlock::RwLock;
use vstd::rwlock::*;
// use vstd::thread::*;
use std::thread::spawn;
verus! {

type ID = nat;

use state_machines_macros::tokenized_state_machine;

tokenized_state_machine!{Bank{
    fields {
        #[sharding(constant)]
        pub total_accounts: nat,

        #[sharding(constant)]
        pub total_amount: nat,

        #[sharding(map)]
        pub account_map: Map<ID, nat>,
    }

    init!{
        initialize(total_accounts: nat, initial_amount: nat) {
            init total_accounts = total_accounts;
            init total_amount = initial_amount * total_accounts;
            init account_map = Map::new(|acc: ID| acc < total_accounts, |acc| initial_amount);
        }
    }

    transition!{
        transfer(acc_from: ID, acc_to: ID, amt: nat) {
            // generated Instance transfer fn will take in 2 account_tokens
            remove account_map -= [acc_from => let from_amt];
            remove account_map -= [acc_to => let to_amt];

            require from_amt >= amt;

            // generated Instance transfer fn will return 2 account_tokens
            add account_map += [acc_from => (from_amt - amt) as nat];
            add account_map += [acc_to => (to_amt + amt) as nat];
        }
    }

    pub open spec(checked) fn range_sum(self, start: ID, end: ID) -> nat
        recommends self.wf(), start <= end <= self.total_accounts
        decreases end - start when start <= end
    {
        if start == end {
            0
        } else {
            self.account_map[start] + self.range_sum(start+1, end)
        }
    }

    #[invariant]
    pub open spec fn wf(&self) -> bool {
        forall |acc: ID| acc < self.total_accounts ==> self.account_map.contains_key(acc)
    }

    #[invariant]
    pub open spec fn preserves_total_amt(&self) -> bool {
        self.range_sum(0, self.total_accounts) == self.total_amount
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, total_accounts: nat, initial_amount: nat) {
        assume(false);
    }

    #[inductive(transfer)]
    fn transfer_inductive(pre: Self, post: Self, acc_from: ID, acc_to: ID, amt: nat) {
        assume(false);
    }
}}

// impl

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
        &&& self.key == info.acc_token@@.key    // token corresponds to_id the right key (ID)
        &&& self.instance == info.acc_token@@.instance // token corresponds to_id the right instance of the protocol
    }
}

struct SimpleBank {
    accounts: Vec<RwLock::<AccountInfo, AccountInv>>, // ID implied by the index
    instance: Tracked<Bank::Instance>,
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
            Tracked(account_map) // perm map
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

    // takes an immutable self bc of interior mutability 
    pub fn maybe_transfer(&self, from_id: usize, to_id: usize, amt: u32)
        requires 
            self.wf(),
            self.valid_id(from_id),
            self.valid_id(to_id),
            from_id != to_id
    {
        let (from_acc, from_handle) = self.accounts[from_id].acquire_write();
        let (to_acc, to_handle) = self.accounts[to_id].acquire_write();

        if from_acc.amt >= amt && to_acc.amt <= u32::MAX - amt {
            let AccountInfo{amt: from_amt, acc_token: Tracked(from_token)} = from_acc;
            let AccountInfo{amt: to_amt, acc_token: Tracked(to_token)}= to_acc;

            // tracked keeps it in proof mode
            let tracked (
                Tracked(new_from_token),
                Tracked(new_to_token) 
            ) = self.instance.borrow().transfer(
                from_id as nat, to_id as nat, 
                amt as nat, from_token, to_token
            );

            let new_from_acc = AccountInfo{amt: (from_amt - amt) as u32, acc_token: Tracked(new_from_token) };
            let new_to_acc = AccountInfo{amt: (to_amt + amt) as u32, acc_token: Tracked(new_to_token) };

            from_handle.release_write(new_from_acc);
            to_handle.release_write(new_to_acc);
        } else {
            from_handle.release_write(from_acc);
            to_handle.release_write(to_acc);
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
}

// fn main() {
//     let bank = SimpleBank::new(10, 10);
//     print_u64(bank.get_total());

//     bank.maybe_transfer(0, 1, 3);
//     bank.maybe_transfer(0, 1, 5);
//     print_u64(bank.check_value(0));
//     print_u64(bank.check_value(1));

//     // bank.maybe_transfer(0, 1, 5);
//     // print_u64(bank.check_value(0));
//     // print_u64(bank.check_value(1));

//     print_u64(bank.check_value(6));
//     // print_u64(bank.check_value(9));
//     print_u64(bank.get_total());

    // let total_accs = 1000;
    // let initial_amt = 100;
    // let num_threads = 10;

    // // how do we freaking get pairs
    // let big_bank = SimpleBank::new(total_accs, initial_amt);
    // print_u64(big_bank.get_total());
// }
} // end of verus!

fn main() {
    let total_accs = 1000;
    let initial_amt = 100;
    let num_threads = 10;

    let big_bank = SimpleBank::new(total_accs, initial_amt);
    let shared_bank = Arc::new(big_bank);
    println!("initial total: {}", shared_bank.get_total());

    let mut handles = Vec::new();

    let ptr_a = shared_bank.clone();
    let ptr_b = shared_bank.clone();
    let ptr_c = shared_bank.clone();
    let ptr_d = shared_bank.clone();

    handles.push(spawn(
        move || {
            let mut i:usize = 0;
            while i < total_accs // makes 100 transfer
            {
                let from = i;
                let to = total_accs - i - 1;
                (*ptr_a).maybe_transfer(from, to, i as u32);
                i = i + 1;
            }
        },
    ));

    handles.push(spawn(
        move || {
            let mut i:usize = 0;
            while i < total_accs // makes 100 transfer
            {
                let from = i;
                let to = total_accs - i - 1;
                (*ptr_d).maybe_transfer(from, to, i as u32);
                i = i + 1;
            }
        },
    ));

    handles.push(spawn(
        move || {
            let mut i:usize = 0;
            while i < 100 // makes 100 transfer
            {
                let from = (i % total_accs) as usize;
                let to = (i+12) % total_accs;
                (*ptr_b).maybe_transfer(from, to, (i*2) as u32);
                i = i + 1;
            }
        },
    ));

    // handles.push(spawn(
    //     move || {
    //         let mut i:usize = 99;
    //         while i > 0 // makes 100 transfer
    //         {
    //             let from =(i % total_accs) as usize;
    //             let to = total_accs-i;
    //             (*ptr_c).maybe_transfer(from, to, 10);
    //             i = i - 1;
    //         }
    //     },
    // ));

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