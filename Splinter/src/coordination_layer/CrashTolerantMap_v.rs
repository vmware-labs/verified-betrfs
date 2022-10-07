#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
#[allow(unused_imports)]
use crate::pervasive::{map::*};

use crate::spec::Option_t::*;
use crate::coordination_layer::StampedMap_v::*;
// use crate::coordination_layer::MessageHistory_v::*;
use crate::coordination_layer::AbstractMap_v::*;

verus! {

type StoreImage = StampedMap;

#[is_variant]
pub enum Ephemeral {
    Unknown,
    Known{ v: AbstractMap::State },
}

state_machine!{ CrashTolerantMap {
    fields { 
        pub persistent: StoreImage,
        pub ephemeral: Ephemeral,
        pub in_flight: Option<StoreImage>,
    }

    init!{
        init() {
            init persistent = StampedMap::empty();
            init ephemeral = Ephemeral::Unknown;
            init in_flight = Option::None;
        }
    }

    

}}
}