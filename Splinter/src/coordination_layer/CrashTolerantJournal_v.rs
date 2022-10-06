#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use crate::coordination_layer::StampedMap_v::*;
use crate::coordination_layer::MessageHistory_v::*;
use crate::coordination_layer::AbstractJournal_v::*;

verus! {

pub type StoreImage = MsgHistory;

// TODO(verus): This is a bug where state machine definitions are only private.
pub type Ephemeral = Option<AbstractJournal::State>;

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
}}
}