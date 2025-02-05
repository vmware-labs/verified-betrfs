#[allow(unused_imports)]    // lost in erasure
use builtin::*;
use vstd::prelude::*;

use vstd::{multiset::Multiset};
use crate::trusted::KVStoreTokenized_v::KVStoreTokenized;
use crate::spec::MapSpec_t::*;
use crate::spec::SystemModel_t::*;
use crate::implementation::ConcreteProgramModel_v::*;

verus!{

// TODO: put into vstd/multiset_lib.rs
pub open spec fn multiset_to_set<V>(m: Multiset<V>) -> Set<V> {
    Set::new(|v| m.contains(v))
}

// Attach the RefinementObligation impl to KVStoreTokenized::State itself;
// don't need an extra type to hold it.
impl RefinementObligation for ConcreteProgramModel {
    type Model = ConcreteProgramModel;

    closed spec fn inv(model: SystemModel::State<Self::Model>) -> bool
    {
        model.inv()
        // &&& model.program.state.requests_have_unique_ids()
        // &&& model.program.state.replies_have_unique_ids()
        // &&& forall |req, reply| model.program.state.requests.contains(req) 
        //     && model.program.state.replies.contains(reply) 
        //     ==> #[trigger] req.id != #[trigger] reply.id

        // &&& forall |req| model.program.state.requests.contains(req)
        //     ==> #[trigger] model.id_history.contains(req.id)
        // &&& forall |reply| model.program.state.replies.contains(reply)
        //     ==> #[trigger] model.id_history.contains(reply.id)

        // &&& model.program.state.atomic_state.wf()
    }

    closed spec fn i(model: SystemModel::State<Self::Model>)
        -> (mapspec: CrashTolerantAsyncMap::State)
    {
        CrashTolerantAsyncMap::State{
            versions: model.program.state.atomic_state.history,
            async_ephemeral: EphemeralState{
                requests: model.program.state.requests.dom(),
                replies: model.program.state.replies.dom(),
            },
            sync_requests: Map::empty(),
        }
    }

    // 
    closed spec fn i_lbl(pre: SystemModel::State<Self::Model>, post: SystemModel::State<Self::Model>, lbl: SystemModel::Label) -> (ctam_lbl: CrashTolerantAsyncMap::Label)
    {
        match lbl {
            SystemModel::Label::ProgramUIOp{op} => {
            match op {
                ProgramUserOp::AcceptRequest{req} =>
                    CrashTolerantAsyncMap::Label::OperateOp{
                        base_op: AsyncMap::Label::RequestOp { req },
                    },
                ProgramUserOp::DeliverReply{reply} =>
                    CrashTolerantAsyncMap::Label::OperateOp{
                        base_op: AsyncMap::Label::ReplyOp { reply },
                    },
                ProgramUserOp::Execute{req, reply} =>
                    CrashTolerantAsyncMap::Label::OperateOp{
                        base_op: AsyncMap::Label::ExecuteOp  { req, reply },
                    },
                // TODO: not currently supported in our transitions
                ProgramUserOp::AcceptSyncRequest{ sync_req_id } =>
                    CrashTolerantAsyncMap::Label::ReqSyncOp{ sync_req_id },
                ProgramUserOp::DeliverSyncReply{ sync_req_id } =>
                    CrashTolerantAsyncMap::Label::ReplySyncOp{ sync_req_id },
            }},
            SystemModel::Label::ProgramDiskOp{ disk_lbl: DiskLabel } =>
                CrashTolerantAsyncMap::Label::Noop{},
            SystemModel::Label::ProgramInternal =>
                CrashTolerantAsyncMap::Label::Noop{},
            SystemModel::Label::DiskInternal => {
                CrashTolerantAsyncMap::Label::Noop{}
                // NOTE: update i_lbl to sometime translate a DiskInternal => SyncExecuteOp
            },
            SystemModel::Label::Crash =>
                CrashTolerantAsyncMap::Label::CrashOp{},
            SystemModel::Label::Noop =>
                CrashTolerantAsyncMap::Label::Noop{},
        }
    }

    proof fn i_lbl_valid(pre: SystemModel::State<Self::Model>, post: SystemModel::State<Self::Model>, lbl: SystemModel::Label, ctam_lbl: CrashTolerantAsyncMap::Label)
    {
        assert( ctam_lbl == Self::i_lbl(pre, post, lbl) );
        assert( lbl.label_correspondance(ctam_lbl) );
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
        reveal(KVStoreTokenized::State::next);
        reveal(KVStoreTokenized::State::next_by);

        reveal(CrashTolerantAsyncMap::State::next);
        reveal(CrashTolerantAsyncMap::State::next_by);
        reveal(AsyncMap::State::next);
        reveal(AsyncMap::State::next_by);
        reveal(MapSpec::State::next);
        reveal(MapSpec::State::next_by);

        // requires:
        assert( SystemModel::State::next(pre, post, lbl) );
        assert( Self::inv(pre) );

        reveal(SystemModel::State::next);
        reveal(SystemModel::State::next_by);
        let step = choose |step| SystemModel::State::next_by(pre, post, lbl, step);

        let ipre = Self::i(pre);
        let ipost = Self::i(post);
        let ilbl = Self::i_lbl(pre, post, lbl);

        match step {
            SystemModel::Step::program_ui(new_program) => {
                match lbl->op {
                    ProgramUserOp::AcceptRequest{req} => {
                        broadcast use insert_new_preserves_cardinality;
                        let new_id = lbl->op.arrow_AcceptRequest_req().id;
                        assert(!pre.id_history.contains(new_id)); // trigger
                        assert(post.program.state._inv());
                        assert(CrashTolerantAsyncMap::State::optionally_append_version(ipre.versions, ipost.versions));

                        let iasync_pre = AsyncMap::State { persistent: ipre.versions.last(), ephemeral: ipre.async_ephemeral };
                        let iasync_post = AsyncMap::State { persistent: ipost.versions.last(), ephemeral: ipost.async_ephemeral };

                        assert(!ipre.async_ephemeral.requests.contains(req));
                        assert(ipre.versions == ipost.versions); // true
                        assert(ipre.async_ephemeral.requests.insert(req) =~= ipost.async_ephemeral.requests);

                        assert(AsyncMap::State::next_by(iasync_pre, iasync_post, ilbl->base_op, AsyncMap::Step::request()));
                        assert(AsyncMap::State::next(iasync_pre, iasync_post, ilbl->base_op));
                        assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, 
                            CrashTolerantAsyncMap::Step::operate(ipost.versions, ipost.async_ephemeral)));
                    },
                    ProgramUserOp::DeliverReply{reply} => {
                        assume(false);
                    },
                    ProgramUserOp::Execute{req, reply} => {
                        assume(false);
                    },
                    ProgramUserOp::AcceptSyncRequest{ sync_req_id } => {
                        // TODO: can't support this until we add this into KVstore tokenized
                        // might be able to just track sync reqs in a different field
                        assume(false); 
                    },
                    ProgramUserOp::DeliverSyncReply{ sync_req_id } => {
                        // TODO: ditto
                        assume(false); 
                    },
                }
                // // auditor's promise: new request contains unique ID
                // require pre.id_history.disjoint(new_id);
                // // new program must be a valid step
                // require T::next(pre.program, new_program, ProgramLabel::UserIO{op: lbl->op});
        
                // update program = new_program;
                // update id_history = pre.id_history.union(new_id);

                assert( CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl) );
            },
            SystemModel::Step::program_disk(new_program, new_disk) => {
                assume( false );
                assert( CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl) );
            },
            SystemModel::Step::program_internal(new_program) => {
                assume( false );
                assert( CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl) );
            },
            SystemModel::Step::disk_internal(new_disk) => {
                assume( false );
                assert( CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl) );
            },
            SystemModel::Step::req_sync(new_program) => {
                assume( false );
                assert( CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl) );
            },
            SystemModel::Step::reply_sync(new_program) => {
                assume( false );
                assert( CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl,
                        CrashTolerantAsyncMap::Step::reply_sync() ) );
                assert( CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl) );
            },
            SystemModel::Step::crash(new_program, new_disk) => {
                // This Implementation, which doesn't actually use the disk, is only "crash
                // tolerant" in the sense that it doesn't support sync. Since we never sync,
                // we maintain the invariant that the first allowed crash Version is the initial
                // state, which of course is exactly what we get when we "recover" without a disk.
                assert( ipost.versions == ipre.versions.get_prefix(ipre.stable_index() + 1) ); // extn equality
                assert( ipost.async_ephemeral == AsyncMap::State::init_ephemeral_state() ); // extn equality
                assert( CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl,
                        CrashTolerantAsyncMap::Step::crash() ) );
            },
            SystemModel::Step::noop() => {
                assert( ipre == ipost );
                assert( CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl,
                        CrashTolerantAsyncMap::Step::noop() ) );
            },
            SystemModel::Step::dummy_to_use_type_params(dummy) => {
            },
        }


//         // ensures:
//         match lbl {
//             SystemModel::Label::ProgramUIOp{op} => {
//                 match op {
//                     ProgramLabel::AcceptRequest{req} => {
//                         let i_post: CrashTolerantAsyncMap::State = Self::i(post);
// //                         let new_versions: FloatingSeq<Version> = FloatingSeq::new(0, 1, |i:int| PersistentState{appv: pre.program.atomic_state.store});
// //                         let new_async_ephemeral: EphemeralState = arbitrary();
//                         let step = CrashTolerantAsyncMap::Step::operate(i_post.versions, i_post.async_ephemeral);

//                         // versions history
//                         // to be fair this should be 

//                         // LEFT OFF:
//                         // I'm looking around for some ghost state, but we don't have a KVStoreTokenized
//                         // here, only a SystemModel/ProgramModel. Where are we going to tuck
//                         // ghost Versions history?
//                         assume(false);
//                         // assert( KVStoreTokenized::show::request(pre, post, KVStoreTokenized::Label::RequestOp{req}, post) );
//                         // assert( pre.program.atomic_state.store == post.program.atomic_state.store );
//                         // assert( i_post.versions == Self::i(pre).versions );
//                         // assert( CrashTolerantAsyncMap::State::next_by(Self::i(pre), i_post, Self::i_lbl(lbl), CrashTolerantAsyncMap::Step::operate(i_post.versions, i_post.async_ephemeral) ) );
//                         // assert( CrashTolerantAsyncMap::State::next_by(Self::i(pre), i_post, Self::i_lbl(lbl), step) );
//                     },
//                     _ => { assume(false); },
//                 }
//             }
//             _ => { assume(false);} ,
//         }
        assert( CrashTolerantAsyncMap::State::next(Self::i(pre), Self::i(post), Self::i_lbl(pre, post, lbl)) );
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

// this is an inv on the system model

impl KVStoreTokenized::State {
//     pub open spec fn _i(self) -> BankSpec::State
//     {
//         BankSpec::State{
//             accounts: self.account_map,
//             requests: self.requests.dom(),
//             replies: self.replies.dom(),
//         }
//     }

    pub closed spec fn _inv(self) -> bool
    {
        &&& self.requests_have_unique_ids()
        &&& self.replies_have_unique_ids()
        &&& forall |req, reply| self.requests.contains(req) && self.replies.contains(reply) 
            ==> #[trigger] req.id != #[trigger] reply.id
    }

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

impl SystemModel::State<ConcreteProgramModel> {
    pub open spec fn inv(self) -> bool
    {
        &&& self.program.state._inv()
        &&& forall |req| self.program.state.requests.contains(req)
            ==> #[trigger] self.id_history.contains(req.id)
        &&& forall |reply| self.program.state.replies.contains(reply)
            ==> #[trigger] self.id_history.contains(reply.id)

        &&& self.program.state.atomic_state.wf()
    }

    // proof fn accept_request_preserves_inv(self, post: Self, 
    //     lbl: SystemModel::Label, new_program: ConcreteProgramModel)
    //     requires 
    //         self.inv(), 
    //         Self::program_ui(self, post, lbl, new_program),
    //         lbl->op is AcceptRequest, 
    //     ensures post.inv(),
    // {
    //     reveal(KVStoreTokenized::State::next);
    //     reveal(KVStoreTokenized::State::next_by);

    //     broadcast use insert_new_preserves_cardinality;

    //     let new_id = lbl->op.arrow_AcceptRequest_req().id;
    //     assert(!self.id_history.contains(new_id)); // trigger
    //     assert(post.program.state._inv());
    // }
}

}
