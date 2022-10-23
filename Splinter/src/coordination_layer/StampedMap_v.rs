#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;

use crate::spec::FloatingSeq_t::*;
use crate::spec::MapSpec_t::*;
use crate::spec::TotalKMMap_t::*;

verus! {
    pub type LSN = nat;

    pub struct Stamped<T>{ 
        pub value: T, 
        pub seq_end: LSN 
    }

    pub type StampedMap = Stamped<TotalKMMap>;

    pub open spec fn empty() -> StampedMap {
        Stamped{ value: empty_total_map(), seq_end: 0}
    }
}


fn main() {}