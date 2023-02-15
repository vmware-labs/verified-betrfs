#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
#[allow(unused_imports)]
use crate::pervasive::{map::*};

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
        // Like they could 
    }

    transition!{
        load_ephemeral_from_persistent(lbl: Label, new_map: AbstractMap::State, map_config: AbstractMap::Config) {
            require lbl.is_LoadEphemeralFromPersistentLabel();
            require pre.ephemeral.is_Unknown();
            require lbl.get_LoadEphemeralFromPersistentLabel_end_lsn() == pre.persistent.seq_end;
            require map_config === AbstractMap::Config::initialize(pre.persistent);
            require AbstractMap::State::init_by(new_map, map_config);
            update ephemeral = Ephemeral::Known{ v: new_map };
        }
    }

    transition!{
        put_records(lbl: Label, new_map: AbstractMap::State, map_step: AbstractMap::Step) {
            require lbl.is_PutRecordsLabel();
            require pre.ephemeral.is_Known();
            // TODO: It seems that map_step and the label both serve the same purpose, and labels are made redundant?
            require map_step === AbstractMap::Step::put();
            require AbstractMap::State::next_by(
                pre.ephemeral.get_Known_v(), 
                new_map,
                AbstractMap::Label::PutLabel{ puts: lbl.get_PutRecordsLabel_records() },
                map_step);
            update ephemeral = Ephemeral::Known{ v: new_map };
        }
    }

    transition!{
        query(lbl: Label, new_map: AbstractMap::State, map_step: AbstractMap::Step) {
            require lbl.is_QueryLabel();
            require pre.ephemeral.is_Known();
            require map_step === AbstractMap::Step::query();
            require AbstractMap::State::next_by(
                pre.ephemeral.get_Known_v(), 
                new_map,
                AbstractMap::Label::QueryLabel{ 
                    end_lsn: lbl.get_QueryLabel_end_lsn(),
                    key: lbl.get_QueryLabel_key(),
                    value: lbl.get_QueryLabel_value()
                },
                map_step);
        }
    }

    transition!{
        freeze_map_internal(lbl: Label, frozen_map: StampedMap, new_map: AbstractMap::State, map_step: AbstractMap::Step) {
            require lbl.is_InternalLabel();
            require pre.ephemeral.is_Known();
            require pre.in_flight.is_None();
            require map_step === AbstractMap::Step::freeze_as();
            require AbstractMap::State::next_by(
                pre.ephemeral.get_Known_v(), 
                new_map,
                AbstractMap::Label::FreezeAsLabel{ stamped_map: frozen_map},
                map_step);
            update ephemeral = Ephemeral::Known{ v: new_map };
            update in_flight = Option::Some(frozen_map);            
        }
    }

    transition!{
        ephemeral_internal(lbl: Label, new_map: AbstractMap::State, map_step: AbstractMap::Step) {
            require lbl.is_InternalLabel();
            require pre.ephemeral.is_Known();
            require map_step === AbstractMap::Step::internal();
            require AbstractMap::State::next_by(
                pre.ephemeral.get_Known_v(), 
                new_map,
                AbstractMap::Label::InternalLabel,
                map_step);
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