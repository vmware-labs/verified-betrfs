#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
use crate::pervasive::{*,map::*};

verus!{

type K = int;  // TODO: this is a placeholder for the Key type
type V = int;  // TODO: this is a placeholder for the Message type

pub open spec fn empty_total_map() -> Map<K, V> {
    // TODO: This body is a placeholder
    Map::new(
        |i: int| i % 10 == 0,
        |i: int| 10 * i,
    )
}
}