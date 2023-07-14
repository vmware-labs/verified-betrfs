use builtin::*;

use builtin_macros::*;

use vstd::{map::*,set::*};
use crate::spec::KeyType_t::*;
use crate::betree::Buffer_v::*;

verus! {

pub struct OffsetMap {
    pub offsets: Map<Key, nat>
}

impl OffsetMap {
    pub open spec(checked) fn is_total(self) -> bool {
        total_keys(self.offsets.dom())
    }

    pub open spec(checked) fn get(self, k: Key) -> nat
        recommends self.is_total()
    {
        self.offsets[k]
    }

    pub open spec(checked) fn filter_for_bottom(self) -> Set<Key>
        recommends self.is_total()
    {
        Set::new(|k| self.offsets[k] == 0)
    }

    pub open spec(checked) fn decrement(self, i: nat) -> OffsetMap
        recommends self.is_total()
    {
        OffsetMap{ offsets: Map::new(|k| true, 
            |k| if i <= self.offsets[k] { (self.offsets[k]-i) as nat } else { 0 as nat} )}
    }
} // end impl offsetmap
}  // end verus!