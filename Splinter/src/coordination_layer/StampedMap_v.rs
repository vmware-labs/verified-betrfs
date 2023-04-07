#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;

use crate::spec::FloatingSeq_t::*;
use crate::spec::MapSpec_t::*;
use crate::spec::TotalKMMap_t::*;

verus! {
    pub type LSN = nat;

    // TODO(jonh): Templating isn't helping, would
    // like to define wf for StampedMap
    pub struct Stamped<T>{ 
        pub value: T, 
        pub seq_end: LSN 
    }

    pub type StampedMap = Stamped<TotalKMMap>;

    pub open spec fn empty() -> StampedMap {
        Stamped{ value: TotalKMMap::empty(), seq_end: 0}
    }
}


fn main() {}
