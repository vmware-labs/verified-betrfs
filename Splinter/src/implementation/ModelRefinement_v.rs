#[allow(unused_imports)]    // lost in erasure
use builtin::*;
use vstd::prelude::*;

use vstd::{multiset::Multiset};
use crate::trusted::KVStoreTokenized_v::KVStoreTokenized;
use crate::spec::MapSpec_t::*;
use crate::spec::SystemModel_t::*;
use crate::spec::FloatingSeq_t::*;

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
        -> (mapspec: CrashTolerantAsyncMap::State)
    {
        let version = Version{ appv: model.program.atomic_state.store };
        let versions = FloatingSeq::new(0, 1, |i| version);
        CrashTolerantAsyncMap::State{
            versions,
            async_ephemeral: EphemeralState{
                requests: model.program.requests.dom(),
                replies: model.program.replies.dom(),
            },
            sync_requests: Map::empty(),
        }
    }

    closed spec fn i_lbl(lbl: SystemModel::Label) -> (ctam_lbl: CrashTolerantAsyncMap::Label)
    {
        match lbl {
            SystemModel::Label::ProgramAsyncOp{ program_lbl } => {
            match program_lbl {
                ProgramLabel::AcceptRequest{req} =>
                    CrashTolerantAsyncMap::Label::OperateOp{
                        base_op: AsyncMap::Label::RequestOp { req },
                    },
                ProgramLabel::DeliverReply{reply} =>
                    CrashTolerantAsyncMap::Label::OperateOp{
                        base_op: AsyncMap::Label::ReplyOp { reply },
                    },
                ProgramLabel::Execute{req, reply} =>
                    CrashTolerantAsyncMap::Label::OperateOp{
                        base_op: AsyncMap::Label::ExecuteOp  { req, reply },
                    },

        // TODO sometimes Internal operations are actually SyncOps. Should
        // those be revealed in ProgramLabel?

        // TODO: dunno.
                ProgramLabel::DiskIO{disk_lbl: DiskLabel} =>
                    CrashTolerantAsyncMap::Label::Noop{},

        // TODO(jialin): How's this different than SystemModel::Label::ProgramInternal?
                ProgramLabel::Internal{} =>
                    CrashTolerantAsyncMap::Label::Noop{},

                ProgramLabel::ReqSync{ sync_req_id } =>
                    CrashTolerantAsyncMap::Label::ReqSyncOp{ sync_req_id },
                ProgramLabel::ReplySync{ sync_req_id } =>
                    CrashTolerantAsyncMap::Label::ReplySyncOp{ sync_req_id },

        // TODO(jialin): Crash appears in SystemModel and in ProgramModel, which is weird.
        // I think ProgramModel::Crash is an error.
                ProgramLabel::Crash =>
                    CrashTolerantAsyncMap::Label::CrashOp{},

            }},
            SystemModel::Label::ProgramDiskOp{ disk_lbl: DiskLabel } =>
                CrashTolerantAsyncMap::Label::Noop{},
            SystemModel::Label::ProgramInternal =>
                CrashTolerantAsyncMap::Label::Noop{},
            SystemModel::Label::DiskInternal =>
                CrashTolerantAsyncMap::Label::Noop{},
            SystemModel::Label::Crash =>
                CrashTolerantAsyncMap::Label::CrashOp{},
            SystemModel::Label::Noop =>
                CrashTolerantAsyncMap::Label::Noop{},
        }
    }

    proof fn i_lbl_valid(lbl: SystemModel::Label, ctam_lbl: CrashTolerantAsyncMap::Label)
    {
//         assert( ctam_lbl == Self::i_lbl(lbl) );
//         assert( lbl.label_correspondance(ctam_lbl) );
    }

    proof fn init_refines(pre: SystemModel::State<Self::Model>)
    {
//         assert( SystemModel::State::initialize(pre, pre.program, pre.disk) );
        // extn equal trigger
        assert( Self::i(pre).async_ephemeral == AsyncMap::State::init_ephemeral_state() );
//         assert( CrashTolerantAsyncMap::State::initialize(Self::i(pre)) );
//         assert( Self::inv(pre) );
    }

    proof fn next_refines(pre: SystemModel::State<Self::Model>, post: SystemModel::State<Self::Model>, lbl: SystemModel::Label)
    {
        reveal(CrashTolerantAsyncMap::State::next);
        reveal(CrashTolerantAsyncMap::State::next_by);
        reveal(AsyncMap::State::next);
        reveal(AsyncMap::State::next_by);
        reveal(MapSpec::State::next);
        reveal(MapSpec::State::next_by);

        // requires:
        assert( SystemModel::State::next(pre, post, lbl) );
        assert( Self::inv(pre) );
        // ensures:
        match lbl {
            SystemModel::Label::ProgramAsyncOp{ program_lbl } => {
                match program_lbl {
                    ProgramLabel::AcceptRequest{req} => {
                        let i_post: CrashTolerantAsyncMap::State = Self::i(post);
//                         let new_versions: FloatingSeq<Version> = FloatingSeq::new(0, 1, |i:int| PersistentState{appv: pre.program.atomic_state.store});
//                         let new_async_ephemeral: EphemeralState = arbitrary();
                        let step = CrashTolerantAsyncMap::Step::operate(i_post.versions, i_post.async_ephemeral);
                        // LEFT OFF:
                        // I'm looking around for some ghost state, but we don't have a KVStoreTokenized
                        // here, only a SystemModel/ProgramModel. Where are we going to tuck
                        // ghost Versions history?
                        assert( KVStoreTokenized::show::request(pre, post, KVStoreTokenized::Label::RequestOp{req}, post) );
                        assert( pre.program.atomic_state.store == post.program.atomic_state.store );
                        assert( i_post.versions == Self::i(pre).versions );
                        assert( CrashTolerantAsyncMap::State::next_by(Self::i(pre), i_post, Self::i_lbl(lbl), CrashTolerantAsyncMap::Step::operate(i_post.versions, i_post.async_ephemeral) ) );
                        assert( CrashTolerantAsyncMap::State::next_by(Self::i(pre), i_post, Self::i_lbl(lbl), step) );
                    },
                    _ => assume(false),
                }
            },
            _ => assume(false),
        }
        assert( CrashTolerantAsyncMap::State::next(Self::i(pre), Self::i(post), Self::i_lbl(lbl)) );
        assume(false);  // left off here
        assert( Self::inv(post) );

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
