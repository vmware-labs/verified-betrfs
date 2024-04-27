// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
/// An AbstractMap (see `AbstractMap_v.rs`) but wrapped with the concept of crashes and recovery.
/// We use this as the abstract crash tolerant map which is coordinated with the
/// CrashAwareJournal in the coordination layer in our refinement proof.

#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
#[allow(unused_imports)]
use vstd::{map::*};

// use crate::spec::Option_t::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;

use crate::abstract_system::StampedMap_v::*;
use crate::abstract_system::MsgHistory_v::*;
use crate::abstract_system::AbstractMap_v::*;

verus! {

type StoreImage = StampedMap;

/// Ephemeral state of crash aware map is the ephemeral (not crash-tolerant)
/// view of the map.
pub enum Ephemeral {
    Unknown,
    Known{ v: AbstractMap::State },
}

state_machine!{ CrashTolerantMap {
    fields {
        /// The persistent view of the map. (Just a StampedMap, so a pure map
        /// data structure). Only modified during commit_complete transitions
        /// (when the persisted snapshot of the map is updated).
        pub persistent: StoreImage,
        /// The ephemeral view of the map. When Known it's an AbstractMap's state
        /// (which just wraps a StampedMap with no extra details). All operations
        /// act on the ephemeral version of the map.
        pub ephemeral: Ephemeral,
        /// in_flight when `Some` represents a snapshot of the map that is going
        /// to be persisted but hasn't been switched over to as our persistent state
        /// yet.
        pub in_flight: Option<StoreImage>,
    }

    init!{
        initialize() {
            init persistent = empty();
            init ephemeral = Ephemeral::Unknown;
            init in_flight = Option::None;
        }
    }

    pub enum Label{
        LoadEphemeralFromPersistentLabel{ end_lsn: LSN },
        PutRecordsLabel{ records: MsgHistory },
        QueryLabel{ end_lsn: LSN, key: Key, value: Value },
        InternalLabel,
        CommitStartLabel{ new_boundary_lsn: LSN },
        CommitCompleteLabel,
        CrashLabel{ keep_in_flight: bool },
    }

    transition!{
        load_ephemeral_from_persistent(lbl: Label) {
            require lbl is LoadEphemeralFromPersistentLabel;
            require pre.ephemeral is Unknown;
            require lbl.arrow_LoadEphemeralFromPersistentLabel_end_lsn() == pre.persistent.seq_end;

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
            require lbl is PutRecordsLabel;
            require pre.ephemeral is Known;
            require AbstractMap::State::next(
                pre.ephemeral->v, 
                new_map,
                AbstractMap::Label::PutLabel{ puts: lbl.arrow_PutRecordsLabel_records() });
            update ephemeral = Ephemeral::Known{ v: new_map };
        }
    }

    transition!{
        query(lbl: Label, new_map: AbstractMap::State) {
            require lbl is QueryLabel;
            require pre.ephemeral is Known;
            require AbstractMap::State::next(
                pre.ephemeral->v, 
                new_map,
                AbstractMap::Label::QueryLabel{ 
                    end_lsn: lbl.arrow_QueryLabel_end_lsn(),
                    key: lbl->key,
                    value: lbl->value
                }
            );
        }
    }

    transition!{
        freeze_map_internal(lbl: Label, frozen_map: StampedMap, new_map: AbstractMap::State) {
            require lbl is InternalLabel;
            require pre.ephemeral is Known;
            require pre.in_flight is None;
            require AbstractMap::State::next(
                pre.ephemeral->v, 
                new_map,
                AbstractMap::Label::FreezeAsLabel{ stamped_map: frozen_map}
            );
            update ephemeral = Ephemeral::Known{ v: new_map };
            update in_flight = Option::Some(frozen_map);            
        }
    }

    transition!{
        ephemeral_internal(lbl: Label, new_map: AbstractMap::State) {
            require lbl is InternalLabel;
            require pre.ephemeral is Known;
            require AbstractMap::State::next(
                pre.ephemeral->v, 
                new_map,
                AbstractMap::Label::InternalLabel,
            );
            update ephemeral = Ephemeral::Known{ v: new_map };   
        }
    }

    transition!{
        commit_start(lbl: Label) {
            require lbl is CommitStartLabel;
            require pre.ephemeral is Known;
            require pre.in_flight is Some;
            require pre.persistent.seq_end <= lbl->new_boundary_lsn;
            require lbl->new_boundary_lsn == pre.in_flight.unwrap().seq_end;
        }
    }

    transition!{
        commit_complete(lbl: Label) {
            require lbl is CommitCompleteLabel;
            require pre.in_flight is Some;
            update persistent = pre.in_flight.unwrap();
            update in_flight = Option::None;
        }
    }

    transition!{
        crash(lbl: Label) {
            require lbl is CrashLabel;
            update ephemeral = Ephemeral::Unknown;
            update in_flight = Option::None;

            // If the system crashes in the time between when a superblock hit the disk and when
            // the program learned about it, then when the program wakes up again, it's going to
            // see what the previous instance thought was "in-flight".
            // (Here we're modeling what in the bottom layer will be a trusted event, which is
            // why it's not ridiculous to "peek" at the disk buffer state via keep_in_flight;
            // by the time we get to the bottom layer of the stack, this entire update will apply
            // to only trusted parts of the system.)
            update persistent = if lbl->keep_in_flight { pre.in_flight.unwrap() } else { pre.persistent };
        }
    }
}}
}
