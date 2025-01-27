use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*; // needed for Ghost, but that gets erased.

use crate::trusted::KVStoreTrait_t::*;
use crate::trusted::ClientAPI_t::*;

verus!{
    pub fn entry<T: KVStoreTrait>() {
        let bank = T::new();
        let api = ClientAPI::new(Ghost(bank.instance()));
        bank.kvstore_main(api);
    }
}

