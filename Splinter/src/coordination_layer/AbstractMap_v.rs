#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

use state_machines_macros::state_machine;

use crate::spec::Messages_t::*;
use crate::spec::TotalKMMap_t::*;
use crate::coordination_layer::StampedMap_v::*;
use crate::coordination_layer::MsgHistory_v::*;

verus! {

state_machine!{ AbstractMap {
    fields { pub stamped_map: StampedMap }

    #[is_variant]
    pub enum Label{
        QueryLabel{ end_lsn: LSN, key: Key, value: Value },
        PutLabel{ puts: MsgHistory},
        FreezeAsLabel{ stamped_map: StampedMap},
        InternalLabel,
    }

    init!{ 
        initialize(persistent_map: StampedMap) {
            init stamped_map = persistent_map;
        }
    }

    transition!{
        query(lbl: Label) {
            require lbl.is_QueryLabel();
            require lbl.get_QueryLabel_end_lsn() == pre.stamped_map.seq_end;
            require lbl.get_QueryLabel_value() === pre.stamped_map.value[lbl.get_QueryLabel_key()].get_Define_value();
        }
    }

    transition!{
        put(lbl: Label) {
            require lbl.is_PutLabel();
            require lbl.get_PutLabel_puts().can_follow(pre.stamped_map.seq_end);
            update stamped_map = MsgHistory::map_plus_history(pre.stamped_map, lbl.get_PutLabel_puts());
        }
    }

    transition!{
        freeze_as(lbl: Label) {
            require lbl.is_FreezeAsLabel();
            require lbl.get_FreezeAsLabel_stamped_map() === pre.stamped_map;
        }
    }

    transition!{
        internal(lbl: Label) {
            require lbl.is_InternalLabel();
        }
    }
}}

}
