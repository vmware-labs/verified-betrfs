#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
use crate::pervasive::{*,map::*};

verus!{

pub type Key = int;  // TODO: this is a placeholder for the Key type
pub type Value = int;  // TODO: this is a placeholder for the Message type

pub type TotalKMMap = Map<Key, Value>;

pub open spec fn empty_total_map() -> Map<Key, Value> {
    // TODO: This body is a placeholder
    Map::new(
        |i: int| i % 10 == 0,
        |i: int| 10 * i,
    )
}
}