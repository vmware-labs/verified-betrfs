// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

use state_machines_macros::state_machine;

use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::abstract_system::StampedMap_v::*;
use crate::abstract_system::MsgHistory_v::*;

verus! {

// AbstractMap is the abstracted view of the B-tree datastructure
// as a map. (For the top-level map spec we're refining to see
// "MapSpec_t.rs").
state_machine!{ AbstractMap {
    // The state of an AbstractMap is just a StampedMap (a map which tracks the most recently
    // applied LSN, the "seq_end").
    fields { pub stamped_map: StampedMap }

    pub enum Label{
        /// When querying, we label the transition with the map LSN (one past the end)
        /// at time of querying, plus the queried key and received value.
        QueryLabel{ end_lsn: LSN, key: Key, value: Value },
        /// We label put transitions with a MsgHistory representing the set of messages
        /// to apply.
        PutLabel{ puts: MsgHistory},
        /// FreezeAs transitions are labeled with the StampedMap state at the time the
        /// transition is taken. (Label allows state machine client to validate/assert
        /// that the version of map they're freezing is correct).
        FreezeAsLabel{ stamped_map: StampedMap},
        /// Internal transitions are unlabeled.
        InternalLabel,
    }

    init!{ 
        initialize(persistent_map: StampedMap) {
            init stamped_map = persistent_map;
        }
    }

    /// A query transition represents querying the value in a map.
    transition!{
        query(lbl: Label) {
            require lbl is QueryLabel;
            require lbl->end_lsn == pre.stamped_map.seq_end;
            require lbl->value === pre.stamped_map.value[lbl->key]->value;
        }
    }

    /// A put transition represents applying a sequence of Msgs (i.e.: a MsgHistory)
    /// to this AbstractMap.
    transition!{
        // Apply the MsgHistory in the label to this.state 
        put(lbl: Label) {
            require lbl is PutLabel;
            require lbl->puts.can_follow(pre.stamped_map.seq_end);
            update stamped_map = MsgHistory::map_plus_history(pre.stamped_map, lbl->puts);
        }
    }

    /// A freeze_as transition represents preparing a snapshot of the map. Doesn't
    /// affect our state, and labeled with the stamped map that's being frozen so
    /// that this freezing can only take place when the labeled stamped_map matches
    /// the current state.
    transition!{
        freeze_as(lbl: Label) {
            require lbl is FreezeAsLabel;
            require lbl->stamped_map === pre.stamped_map;
        }
    }

    /// Internal transition for non-public-facing updates.
    transition!{
        internal(lbl: Label) {
            require lbl is InternalLabel;
        }
    }
}}

}
