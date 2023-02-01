#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

use crate::pervasive::{*,map::*};
use crate::spec::Messages_t::*;
use crate::spec::TotalKMMap_t::*;

verus! {
    pub struct Buffer { 
        pub mapp: Map<Key, Message>
    }

    // TODO: comment this out and do the thing
    // impl Buffer { 
    //     pub open spec fn query(self, key: Key) -> Message {
    //         if self.mapp.dom().contains(key) {
    //             self.mapp[key]
    //         } else {
    //             Update(nop_delta())
    //         }
    //     }
    // }

// // TODO: These are placeholders
// pub type Value = int;
// pub type Delta = int;

// // TODO(jonh): Need to genericize the types of Key, Value; and then we'll need to axiomitify /
// // leave-unspecified a default value
// pub open spec fn default_value() -> Value {
//     0
// }

// #[is_variant]
// pub enum Message {
//     Define{ value: Value },
//     Update{ delta: Delta},
// }

// impl Message {
//     pub open spec fn merge(self, new: Message) -> Message {
//         self  // TODO: This is a placeholder
//     }

//     pub open spec fn empty() -> Message {
//         Message::Define{ value: 0 }  // TODO: This is a placeholder
//     }
// }

}