#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use crate::spec::KeyType_t::*;

verus! {
#[is_variant]
pub enum SplitRequest {
    SplitLeaf{child_idx: nat, split_key: Key},
    SplitIndex{child_idx: nat, child_pivot_idx: nat}
}
} // end verus!
