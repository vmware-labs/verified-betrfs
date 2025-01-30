#[allow(unused_imports)]    // lost in erasure
use builtin::*;
use vstd::prelude::*;

use vstd::{multiset::Multiset};
use crate::trusted::KVStoreTokenized_v::KVStoreTokenized;
use crate::spec::MapSpec_t::*;
use crate::spec::SystemModel_t::*;

verus!{

// NOTE: KVStoreTokenized should just use program label as its own
impl ProgramLabel {
    pub open spec fn to_kv_lbl(self) -> KVStoreTokenized::Label{
        match self {
            ProgramLabel::AcceptRequest{req} => KVStoreTokenized::Label::RequestOp{req},
            ProgramLabel::DeliverReply{reply} => KVStoreTokenized::Label::ReplyOp{reply},
            ProgramLabel::Execute{req, reply} => KVStoreTokenized::Label::ExecuteOp{req, reply},
            _ => KVStoreTokenized::Label::InternalOp,
        }
    }
}

impl ProgramModel for KVStoreTokenized::State {
    open spec fn init(pre: Self, disk: DiskModel) -> bool
    {
        Self::initialize(pre)
    }

    open spec fn next(pre: Self, post: Self, lbl: ProgramLabel) -> bool
    {
        Self::next(pre, post, lbl.to_kv_lbl())
    }
}

// TODO: put into vstd/multiset_lib.rs
pub open spec fn multiset_to_set<V>(m: Multiset<V>) -> Set<V> {
    Set::new(|v| m.contains(v))
}


// Attach the RefinementObligation impl to KVStoreTokenized::State itself;
// don't need an extra type to hold it.
impl RefinementObligation for KVStoreTokenized::State {
    type Model = Self;

    closed spec fn inv(model: SystemModel::State<Self::Model>) -> bool
    {
        &&& model.program.requests_have_unique_ids()
        &&& model.program.replies_have_unique_ids()
        &&& forall |req, reply| model.program.requests.contains(req) 
            && model.program.replies.contains(reply) 
            ==> #[trigger] req.id != #[trigger] reply.id

        &&& forall |req| model.program.requests.contains(req)
            ==> #[trigger] model.id_history.contains(req.id)
        &&& forall |reply| model.program.replies.contains(reply)
            ==> #[trigger] model.id_history.contains(reply.id)
    }
 
    closed spec fn i(model: SystemModel::State<Self::Model>)
        -> (ctam: CrashTolerantAsyncMap::State)
    {
        // SystemModel wraps program & disk, we shall ignore disk for now
        // Model is a KVStoreTokenized::State (from type assignment above in this file)
        // We're going to pluck the atomic_state out and that's almost the ctam,
        // except we need to squirt the requests & replies into it.
        
        CrashTolerantAsyncMap::State{
            versions: model.program.atomic_state.store.versions,
            async_ephemeral: EphemeralState{
                requests: model.program.requests.dom(),
                replies: model.program.replies.dom(),
            },
            sync_requests: Map::empty(),
        }
    }

    closed spec fn i_lbl(lbl: SystemModel::Label) -> (ctam_lbl: CrashTolerantAsyncMap::Label)
    {
        arbitrary()
    }

    proof fn i_lbl_valid(lbl: SystemModel::Label, ctam_lbl: CrashTolerantAsyncMap::Label)
    {
        assume(false);
    }

    proof fn init_refines(pre: SystemModel::State<Self::Model>)
    {
        assume(false);
    }

    proof fn next_refines(pre: SystemModel::State<Self::Model>, post: SystemModel::State<Self::Model>, lbl: SystemModel::Label)
    {
//         reveal(SystemModel::State::next);
//         reveal(SystemModel::State::next_by);
// 
//         reveal(KVStoreTokenized::State::next);
//         reveal(KVStoreTokenized::State::next_by);

        assume(false);
    }
}

pub open spec(checked) fn all_elems_single<V>(m: Multiset<V>) -> bool
{
    forall |e| #[trigger] m.contains(e) ==> m.count(e) == 1
}

broadcast proof fn insert_new_preserves_cardinality<V>(m: Multiset<V>, new: V)
    requires all_elems_single(m), !m.contains(new)
    ensures #[trigger] all_elems_single(m.insert(new))
{
    let post_m = m.insert(new);
    assert forall |e| #[trigger] post_m.contains(e)
    implies post_m.count(e) == 1
    by {
        if e != new {
            assert(m.contains(e)); // trigger
        }
    }
}

impl KVStoreTokenized::State {
//     pub open spec fn _i(self) -> BankSpec::State
//     {
//         BankSpec::State{
//             accounts: self.account_map,
//             requests: self.requests.dom(),
//             replies: self.replies.dom(),
//         }
//     }
// 
//     closed spec fn _inv(self) -> bool
//     {
//         &&& self.requests_have_unique_ids()
//         &&& self.replies_have_unique_ids()
//         &&& forall |req, reply| self.requests.contains(req) && self.replies.contains(reply) 
//             ==> #[trigger] req.id != #[trigger] reply.id
//     }

    pub open spec(checked) fn requests_have_unique_ids(self) -> bool 
    {
        &&& all_elems_single(self.requests)
        &&& forall |req1, req2| self.requests.contains(req1) 
            && self.requests.contains(req2) 
            && #[trigger] req1.id == #[trigger] req2.id
            ==> req1 == req2
    }

    pub open spec(checked) fn replies_have_unique_ids(self) -> bool 
    {
        &&& all_elems_single(self.replies)
        &&& forall |reply1, reply2| self.replies.contains(reply1) 
            && self.replies.contains(reply2) 
            && #[trigger] reply1.id == #[trigger] reply2.id
            ==> reply1 == reply2
    }
}

}
