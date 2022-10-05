#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

use state_machines_macros::state_machine;

use crate::spec::TotalKMMap_t::*;
use crate::coordination_layer::StampedMap_v::*;
use crate::coordination_layer::MessageHistory_v::*;

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
        Init(persistent_map: StampedMap) {
            init stamped_map = persistent_map;
        }
    }

    // TODO: Complete this
    transition!{
        query(lbl: Label) {
            require lbl.is_QueryLabel();
            require lbl.get_QueryLabel_end_lsn() == pre.stamped_map.seq_end;
            require lbl.get_QueryLabel_value() === pre.stamped_map.value[lbl.get_QueryLabel_key()];
        }
    }

    // transition!{
    //     query(lbl: Label) {
    //         require lbl.is_QueryLabel();
    //         require lbl.get_QueryLabel_end_lsn == pre.stamped_map.seq_end;
    //         require lbl.get_QueryLabel_value == pre.stamped_map.value[lbl.get_QueryLabel_key()].value;
    //     }
    // }
    


}}
}