#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
use crate::pervasive::{*,map::*};

verus!{

// TODO: This is a placeholder for the dafny Message type
pub struct Message {
    pub dummy: int 
}

impl Message {
    pub open spec fn merge(self, new: Message) -> Message {
        self  // TODO: This is a placeholder
    }

    pub open spec fn empty() -> Message {
        Message{ dummy: 0 }
    }
}

pub type Key = int;  // TODO: this is a placeholder for the Key type
pub type Value = Message;  // TODO: this is a placeholder for the Message type

pub type TotalKMMap = Map<Key, Value>;



pub open spec fn empty_total_map() -> Map<Key, Value> {
    // TODO: This body is a placeholder
    // TODO(verus): Should not have to declare binder twice.
    Map::new(
        |i: int| true,
        |i: int| Message::empty(),
    )
}
}