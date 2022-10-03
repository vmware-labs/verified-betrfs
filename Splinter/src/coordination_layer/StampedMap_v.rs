#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;

use crate::spec::FloatingSeq_t::*;
use crate::spec::MapSpec_t::*;
use crate::spec::TotalKMMap_t::*;

verus! {
    type LSN = nat;

    struct Stamped<T>{ value: T, seq_end: LSN }

    type StampedMap = Stamped<TotalKMMap>;

    spec fn empty() -> StampedMap {
        Stamped{ value: empty_total_map(), seq_end: 0}
    }
}


fn main() {}