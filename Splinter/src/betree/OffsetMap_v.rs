#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

use crate::pervasive::{*,map::*,set::*};
use crate::spec::TotalKMMap_t::*;
use crate::betree::Buffer_v::*;

verus! {

pub struct OffsetMap {
    pub offsets: Map<Key, nat>
}

impl OffsetMap {
    pub open spec fn is_total(self) -> bool {
        total_keys(self.offsets.dom())
    }

    pub open spec fn get(self, k: Key) -> nat
        recommends self.is_total()
    {
        self.offsets[k]
    }

    pub open spec fn filter_for_bottom(self) -> Set<Key>
        recommends self.is_total()
    {
        Set::new(|k| self.offsets[k] == 0)
    }

    pub open spec fn decrement(self, i: nat) -> OffsetMap
        recommends self.is_total()
    {
        OffsetMap{ offsets: Map::new(|k| true, 
            |k| if i <= self.offsets[k] { (self.offsets[k]-i) as nat } else { 0 as nat} )}
    }
} // end impl offsetmap
}  // end verus!