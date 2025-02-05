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
                let iasync_pre = AsyncMap::State { persistent: ipre.versions.last(), ephemeral: ipre.async_ephemeral };
                let iasync_post = AsyncMap::State { persistent: ipost.versions.last(), ephemeral: ipost.async_ephemeral };

                match lbl->op {
                    ProgramUserOp::AcceptRequest{req} => {
                        broadcast use insert_new_preserves_cardinality;
                        let new_id = lbl->op.arrow_AcceptRequest_req().id;
                        assert(!pre.id_history.contains(new_id)); // trigger
                        assert(post.program.state._inv());
                        assert(post.inv());
                        assert(CrashTolerantAsyncMap::State::optionally_append_version(ipre.versions, ipost.versions));

                        assert(!ipre.async_ephemeral.requests.contains(req));
                        assert(ipre.versions == ipost.versions); // true
                        assert(ipre.async_ephemeral.requests.insert(req) =~= ipost.async_ephemeral.requests);

                        assert(AsyncMap::State::next_by(iasync_pre, iasync_post, ilbl->base_op, AsyncMap::Step::request()));
                        assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, 
                            CrashTolerantAsyncMap::Step::operate(ipost.versions, ipost.async_ephemeral)));
                    },
                    ProgramUserOp::DeliverReply{reply} => {
                        assert(post.program.state._inv()) by {
                            assert(forall |r| #[trigger] post.program.state.replies.contains(r) 
                                ==> pre.program.state.replies.contains(r));
                        }
                        assert(post.inv());
                        assert(ipre.async_ephemeral.replies.contains(reply));
                        assert(!post.program.state.replies.contains(reply)) by {
                            if (post.program.state.replies.contains(reply)) {
                                assert(pre.program.state.replies.contains(reply));
                                assert(pre.program.state.replies.count(reply) > 1);
                                assert(false);
                            }
                        }
                        assert(ipost.async_ephemeral.replies =~= ipre.async_ephemeral.replies.remove(reply));

                        assert(AsyncMap::State::next_by(iasync_pre, iasync_post, ilbl->base_op, AsyncMap::Step::reply()));
                        assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, 
                            CrashTolerantAsyncMap::Step::operate(ipost.versions, ipost.async_ephemeral)));
                    },
                    ProgramUserOp::Execute{req, reply} => {
                        let kv_lbl = ProgramLabel::UserIO{op: lbl->op}.to_kv_lbl();
                        assert(kv_lbl is ExecuteOp);
                        assert(KVStoreTokenized::State::next(pre.program.state, post.program.state, kv_lbl));

                        let map_lbl = choose |map_lbl| #[trigger] KVStoreTokenized::State::next_by(
                                pre.program.state, post.program.state, kv_lbl, 
                                KVStoreTokenized::Step::execute_transition(post.program.state.atomic_state, map_lbl));

                        pre.program.state.execute_transition_magic(post.program.state, kv_lbl, map_lbl);
                        assert(post.program.state._inv());
                        assert(post.inv());

                        assert(ipost.async_ephemeral.requests =~= ipre.async_ephemeral.requests.remove(req));
                        assert(ipost.async_ephemeral.replies =~= ipre.async_ephemeral.replies.insert(reply));
                        assert(AsyncMap::State::next_by(iasync_pre, iasync_post, ilbl->base_op, 
                            AsyncMap::Step::execute(map_lbl, iasync_post.persistent)));                        
                        assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, 
                                CrashTolerantAsyncMap::Step::operate(ipost.versions, ipost.async_ephemeral)));
                    },
                    ProgramUserOp::AcceptSyncRequest{ sync_req_id } => {
                        // TODO: can't support this until we add this into KVstore tokenized
                        // might be able to just track sync reqs in a different field
                        assume( CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl) );
                    },
                    ProgramUserOp::DeliverSyncReply{ sync_req_id } => {
                        // TODO: ditto
                        assume( CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl) );
                    },
                }
            },
            SystemModel::Step::program_disk(new_program, new_disk) => {
                assert(new_program == pre.program);
                assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, 
                    CrashTolerantAsyncMap::Step::noop()));
                assert( Self::inv(post) );
            },
            SystemModel::Step::program_internal(new_program) => {
                assert(new_program == pre.program);
                assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, 
                    CrashTolerantAsyncMap::Step::noop()));
                assert( Self::inv(post) );
            },
            SystemModel::Step::disk_internal(new_disk) => {
                assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, 
                    CrashTolerantAsyncMap::Step::noop()));
                assert( Self::inv(post) );
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
                assert( Self::inv(post) );
            },
            SystemModel::Step::noop() => {
                assert( ipre == ipost );
                assert( CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl,
                        CrashTolerantAsyncMap::Step::noop() ) );
                assert( Self::inv(post) );
            },
            SystemModel::Step::dummy_to_use_type_params(dummy) => {
            },
        }
        assert( CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl) );
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
    pub closed spec fn _inv(self) -> bool
    {
        &&& self.wf()
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

    proof fn execute_transition_magic(self, post: Self, lbl: KVStoreTokenized::Label, map_lbl: MapSpec::Label)
        requires
            self._inv(), 
            Self::execute_transition(self, post, lbl, post.atomic_state, map_lbl),
        ensures 
            post._inv(),
            CrashTolerantAsyncMap::State::optionally_append_version(
                self.atomic_state.history, post.atomic_state.history),
    {
        broadcast use insert_new_preserves_cardinality;
        reveal(MapSpec::State::next);
        reveal(MapSpec::State::next_by);

        let req = lbl.arrow_ExecuteOp_req();
        let reply = lbl.arrow_ExecuteOp_reply();

        KVStoreTokenized::State::execute_transition_inductive(
            self, post, lbl, post.atomic_state, map_lbl);
        assert(forall |req| #[trigger] post.requests.contains(req) 
            ==> self.requests.contains(req));
        assert(post._inv());

        let history = self.atomic_state.history;
        let post_history = post.atomic_state.history;

        if history.len() == post_history.len() {
            assert(post_history.get_prefix(history.len()) == post_history); // trigger
        } else {
            assert(post_history.get_prefix(history.len()) == history); // trigger
        }
        assert(CrashTolerantAsyncMap::State::optionally_append_version(history, post_history));
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
        // &&& self.program.state.atomic_state.wf()
    }
}
}
