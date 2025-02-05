#[allow(unused_imports)]    // lost in erasure
use builtin::*;
use vstd::prelude::*;

use crate::trusted::KVStoreTokenized_v::KVStoreTokenized;
use crate::spec::SystemModel_t::*;

verus!{

pub struct ConcreteProgramModel {
    pub state: KVStoreTokenized::State,
}

impl ConcreteProgramModel {
}

impl ProgramModel for ConcreteProgramModel {
    open spec fn is_mkfs(disk: DiskModel) -> bool
    {
        true // check superblock content
    }

    open spec fn init(pre: Self) -> bool
    {
        &&& KVStoreTokenized::State::initialize(pre.state)
    }

    open spec fn next(pre: Self, post: Self, lbl: ProgramLabel) -> bool
    {
        KVStoreTokenized::State::next(pre.state, post.state, lbl.to_kv_lbl())
        // TODO and update history
    }
}

}
