#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use crate::spec::Option_t::*;
use crate::coordination_layer::StampedMap_v::*;
use crate::coordination_layer::MessageHistory_v::*;
use crate::coordination_layer::AbstractJournal_v::*;

verus! {

pub type StoreImage = MsgHistory;

// TODO: Could use option types? But they are not supported in verus
#[is_variant]
pub enum Ephemeral {
    Unknown,
    Known{ v: AbstractJournal::State },
}

state_machine!{ CrashTolerantJournal {
    fields { 
        pub persistent: StoreImage,
        pub ephemeral: Ephemeral,
        pub in_flight: Option<StoreImage>
    }

    #[is_variant]  // TODO: verus! should always make enum variants
    pub enum Label{
        LoadEphemeralFromPersistentLabel,
        ReadForRecoveryLabel{ records: MsgHistory},
        QueryEndLsnLabel{ end_lsn: LSN },
        PutLabel{ messages: MsgHistory },
        InternalLabel,
        QueryLsnPersistenceLabel{ sync_lsn: LSN },
        CommitStartLabel{ new_boundary_lsn: LSN, max_lsn: LSN },
        CommitCompleteLabel{ require_end: LSN },
        CrashLabel,
    }

    transition!{
        load_ephemeral_from_persistent(lbl: Label, new_ephemeral: AbstractJournal::State, ephemeral_step: AbstractJournal::Config) {
            require lbl.is_LoadEphemeralFromPersistentLabel();
            require pre.ephemeral.is_Unknown();
            // Not sure if this init_by usage is right. Awaiting slack confirmation
            require AbstractJournal::State::init_by(new_ephemeral, ephemeral_step);
        }
    }



    

}}
}