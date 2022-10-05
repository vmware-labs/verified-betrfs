#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
use crate::pervasive::{*,map::*};

use crate::spec::Messages_t::*;

verus!{

pub type Key = int;  // TODO: this is a placeholder for the Key type

pub type TotalKMMap = Map<Key, Message>;

pub open spec fn empty_total_map() -> Map<Key, Message> {
    // TODO: This body is a placeholder
    // TODO(verus): Should not have to declare binder twice.
    Map::new(
        |i: int| true,
        |i: int| Message::empty(),
    )
}
}