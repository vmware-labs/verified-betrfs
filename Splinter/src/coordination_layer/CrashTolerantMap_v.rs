#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
#[allow(unused_imports)]
use vstd::{map::*};

use crate::spec::Option_t::*;
use crate::spec::TotalKMMap_t::*;
use crate::spec::Messages_t::*;
use crate::coordination_layer::StampedMap_v::*;
use crate::coordination_layer::MsgHistory_v::*;
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
        initialize() {
            init persistent = empty();
            init ephemeral = Ephemeral::Unknown;
            init in_flight = Option::None;
        }
    }

    #[is_variant]
    pub enum Label{
        LoadEphemeralFromPersistentLabel{ end_lsn: LSN },
        PutRecordsLabel{ records: MsgHistory },
        QueryLabel{ end_lsn: LSN, key: Key, value: Value },
        InternalLabel,
        CommitStartLabel{ new_boundary_lsn: LSN },
        CommitCompleteLabel,
        CrashLabel,
    }

    transition!{
        load_ephemeral_from_persistent(lbl: Label) {
            require lbl.is_LoadEphemeralFromPersistentLabel();
            require pre.ephemeral.is_Unknown();
            require lbl.get_LoadEphemeralFromPersistentLabel_end_lsn() == pre.persistent.seq_end;

            let new_abstract_map = AbstractMap::State {
                stamped_map: pre.persistent,
            };

            // All of this feels a little silly, something wonky about
            // how the init transition of AbstractMap is defined. Note that
            // these requires aren't actually necessary for the update line
            // below as it's currently defined, but it will catch if there are
            // any changes to how a valid "initialization" is defined by the
            // AbstractMap state machine.
            // We want something like labels here instead probably.
            require AbstractMap::State::init_by(
                new_abstract_map,
                AbstractMap::Config::initialize(pre.persistent));

            // Load entire persistent map into ephemeral state
            update ephemeral = Ephemeral::Known {
                v: new_abstract_map
            };
        }
    }

    transition!{
        // Apply the commands in the message history in the given label
        // to this map
        put_records(lbl: Label, new_map: AbstractMap::State) {
            require lbl.is_PutRecordsLabel();
            require pre.ephemeral.is_Known();
            require AbstractMap::State::next(
                pre.ephemeral.get_Known_v(), 
                new_map,
                AbstractMap::Label::PutLabel{ puts: lbl.get_PutRecordsLabel_records() });
            update ephemeral = Ephemeral::Known{ v: new_map };
        }
    }

    transition!{
        query(lbl: Label, new_map: AbstractMap::State) {
            require lbl.is_QueryLabel();
            require pre.ephemeral.is_Known();
            require AbstractMap::State::next(
                pre.ephemeral.get_Known_v(), 
                new_map,
                AbstractMap::Label::QueryLabel{ 
                    end_lsn: lbl.get_QueryLabel_end_lsn(),
                    key: lbl.get_QueryLabel_key(),
                    value: lbl.get_QueryLabel_value()
                }
            );
        }
    }

    transition!{
        freeze_map_internal(lbl: Label, frozen_map: StampedMap, new_map: AbstractMap::State) {
            require lbl.is_InternalLabel();
            require pre.ephemeral.is_Known();
            require pre.in_flight.is_None();
            require AbstractMap::State::next(
                pre.ephemeral.get_Known_v(), 
                new_map,
                AbstractMap::Label::FreezeAsLabel{ stamped_map: frozen_map}
            );
            update ephemeral = Ephemeral::Known{ v: new_map };
            update in_flight = Option::Some(frozen_map);            
        }
    }

    transition!{
        ephemeral_internal(lbl: Label, new_map: AbstractMap::State) {
            require lbl.is_InternalLabel();
            require pre.ephemeral.is_Known();
            require AbstractMap::State::next(
                pre.ephemeral.get_Known_v(), 
                new_map,
                AbstractMap::Label::InternalLabel,
            );
            update ephemeral = Ephemeral::Known{ v: new_map };   
        }
    }

    transition!{
        commit_start(lbl: Label) {
            require lbl.is_CommitStartLabel();
            require pre.ephemeral.is_Known();
            require pre.in_flight.is_Some();
            require pre.persistent.seq_end <= lbl.get_CommitStartLabel_new_boundary_lsn();
            require lbl.get_CommitStartLabel_new_boundary_lsn() == pre.in_flight.get_Some_0().seq_end;
        }
    }

    transition!{
        commit_complete(lbl: Label) {
            require lbl.is_CommitCompleteLabel();
            require pre.in_flight.is_Some();
            update persistent = pre.in_flight.get_Some_0();
            update in_flight = Option::None;
        }
    }

    transition!{
        crash(lbl: Label) {
            require lbl.is_CrashLabel();
            update ephemeral = Ephemeral::Unknown;
            update in_flight = Option::None;
        }
    }
}}
}