#[allow(unused_imports)]    // lost in erasure
use builtin::*;
use vstd::prelude::*;

use vstd::{multiset::Multiset, set_lib::*};
use crate::spec::AsyncDisk_t::*;
use crate::spec::MapSpec_t::*;
use crate::trusted::SystemModel_t::*;
use crate::trusted::RefinementObligation_t::*;
use crate::trusted::ProgramModelTrait_t::*;
use crate::implementation::AtomicState_v::*;
use crate::implementation::ConcreteProgramModel_v::*;
use crate::implementation::MultisetMapRelation_v::*;
use crate::implementation::DiskLayout_v::*;

verus!{

// TODO: put into vstd/multiset_lib.rs
pub open spec fn multiset_to_set<V>(m: Multiset<V>) -> Set<V> {
    Set::new(|v| m.contains(v))
}

broadcast proof fn unmarshall_marshall(sb: Superblock)
    ensures sb == #[trigger] spec_unmarshall(spec_marshall(sb))
{
    assume(false);
}

impl AtomicState {
    // pub open spec fn wf(self) -> bool {
    //     self.recovery_state is RecoveryComplete ==> {
    //         &&& self.history.is_active(self.history.len()-1)
    //         &&& forall |i| #[trigger] self.history.is_active(i) ==> self.history[i].appv.invariant()
    //         &&& self.in_flight is Some ==> {
    //             self.history.is_active(self.in_flight.unwrap().version as int)
    //         }
    //         &&& self.history.is_active(self.persistent_version as int)
    //     }
    // }

//     pub proof fn disk_transition_preserves_wf(pre: Self, post: Self, disk_event_lbl: DiskEvent, disk_lbl: AsyncDisk::Label, disk_req_id: ID)
//     requires
//         pre.wf(),
//         Self::disk_transition(pre, post, disk_event_lbl, disk_lbl, disk_req_id),
//     ensures
//         post.wf(),
//     {
//         if post.recovery_state is RecoveryComplete {
//             assume(false);
//             match disk_event_lbl {
//                 DiskEvent::InitiateRecovery{} => {
//                     assert( post.wf() );
//                 },
//                 DiskEvent::CompleteRecovery{raw_page} => {
//                     assert( post.history.is_active(post.history.len()-1) );
//                     assert forall |i| #[trigger] post.history.is_active(i) implies post.history[i].appv.invariant() by {
//                         let superblock = spec_unmarshall(raw_page);
//                         assert( i == superblock.version_index );
//                         assert( post.history[i] == superblock.store );
//                         assert( superblock.store.appv.invariant() ) by {
//                             // TODO remember that invariant survives disk
//                             assume( false );
//                         }
//                     }
//                 },
//                 DiskEvent::ExecuteSyncBegin{} => {
//                     assert( post.wf() );
//                 },
//                 DiskEvent::ExecuteSyncEnd{} => {
//                     assert( pre.in_flight is Some ) by {
//                         // TODO remember that in_flight is Some whenever an IO is in
//                         // flight. This seems like a system property, not a wf, since we can't
//                         // see the IO buffer from here. How are we gonna get this wf down
//                         // to Implementation!? Maybe it moves to inv, so Impl doesn't need to
//                         // show it as part of wf?
//                         assume( false );
//                     }
//                     let new_version = pre.in_flight.unwrap().version;
// //                     assert( pre.history.is_active(new_version as int) );
// //                     assert( post.history.is_active(post.history.len()-1) );
// //                     assert forall |i| #[trigger] post.history.is_active(i) implies post.history[i].appv.invariant() by {
// //                         assert( pre.history.is_active(i) );
// //                     }
//                     assert( post.wf() );
//                 },
//             }
//         }
//     }
}

impl SystemModel::State<ConcreteProgramModel>  {
    pub open spec fn inv(self) -> bool
    {
        &&& self.program.state.wf()
        &&& self.disk.inv()

        &&& self.in_flight_sb_disk_relation()
        &&& self.persistent_sb_disk_relation()

        // &&& self.no_action_while_awaiting_sb() // why should a property like this be an inv?
        &&& self.at_most_one_oustanding_request_per_address()

        &&& self.requests_have_unique_ids()
        &&& self.replies_have_unique_ids()
        &&& self.requests_replies_id_disjoint()

        &&& all_elems_single(self.sync_requests)
        &&& self.program.state.client_ready() ==>   
            self.sync_requests.dom() == self.program.state.sync_req_map.dom()
    }

    pub open spec fn in_flight_sb_disk_relation(self) -> bool
    {
        self.program.state.client_ready() ==> {
            let in_flight = self.program.state.in_flight;
            &&& in_flight is Some ==> {
                let id = in_flight.unwrap().req_id;
                &&& (self.disk.requests.contains_key(id) || self.disk.responses.contains_key(id))
                &&& self.disk.requests.contains_key(id) ==> 
                    self.disk.requests[id] == DiskRequest::WriteReq{
                        to: spec_superblock_addr(), 
                        data: spec_marshall(self.program.state.in_flight_sb())
                    }
                &&& self.disk.responses.contains_key(id) ==> 
                    self.disk.responses[id] == DiskResponse::WriteResp{}
            }
        }
    }

    pub open spec fn persistent_sb_disk_relation(self) -> bool
    {
        &&& self.disk.content.contains_key(spec_superblock_addr())
        &&& self.program.state.client_ready() ==> {
                self.disk.content[spec_superblock_addr()] == 
                spec_marshall(self.program.state.persistent_sb())
            }
    }

    pub open spec fn at_most_one_oustanding_request_per_address(self) -> bool
    {
        forall |id1, id2|  #[trigger] self.disk.requests.contains_key(id1) && #[trigger] self.disk.requests.contains_key(id2) 
            && id1 != id2 ==> self.disk.requests[id1].addr() != self.disk.requests[id2].addr() 
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

    pub open spec(checked) fn requests_replies_id_disjoint(self) -> bool 
    {
        forall |req, reply| self.requests.contains(req) && self.replies.contains(reply) 
            ==> #[trigger] req.id != #[trigger] reply.id
    }

    // interpretation given no ephemeral state and only on persistent disk
    closed spec(checked) fn i_persistent(self) -> (mapspec: CrashTolerantAsyncMap::State)
    recommends
        !self.program.state.client_ready(),
        self.disk.content.contains_key(spec_superblock_addr()),    // quash recommendation not met
    {
        let sb = spec_unmarshall(self.disk.content[spec_superblock_addr()]);
        let state = sb.store;
        CrashTolerantAsyncMap::State{
            versions: singleton_floating_seq(sb.version_index, sb.store.appv.kmmap),
            async_ephemeral: AsyncMap::State::init_ephemeral_state(),
            sync_requests: Map::empty(),
        }
    }

    // ephemeral depends on whether things have landed on disk
    closed spec(checked) fn i_ephemeral(self) -> (mapspec: CrashTolerantAsyncMap::State)
    recommends 
        self.program.state.wf(),
        self.program.state.client_ready(), 
    {
        let model = self.program.state;
        let actual_versions = 
            if model.in_flight is Some 
                && self.disk.responses.contains_key(model.in_flight.unwrap().req_id) 
            {
                model.history.get_suffix(model.in_flight.unwrap().version as int)
            } else { 
                model.history
            };

        CrashTolerantAsyncMap::State{
            versions: actual_versions,
            async_ephemeral: EphemeralState{
                requests: self.requests.dom(),
                replies: self.replies.dom(),
            },
            sync_requests: self.program.state.sync_req_map,
            // requests are ones that have been tracked by 
            // sync_requests: multiset_to_map(self.sync_requests),
         }
    }

    closed spec fn sb_landed(self: Self, post: Self) -> bool
    {
        let state = self.program.state;
        &&& state.in_flight is Some
        &&& !self.disk.responses.contains_key(state.in_flight.unwrap().req_id)
        &&& post.disk.responses.contains_key(state.in_flight.unwrap().req_id)
    }
}

pub struct RefinementProof{}

impl RefinementObligation<ConcreteProgramModel> for RefinementProof {

    closed spec fn inv(model: SystemModel::State<ConcreteProgramModel>) -> bool
    {
        model.inv()
    }

    // interpretation depends on pre and post 
    closed spec fn i(model: SystemModel::State<ConcreteProgramModel>) -> (mapspec: CrashTolerantAsyncMap::State)
    {
        if model.program.state.client_ready() {
            model.i_ephemeral()
        } else {
            model.i_persistent()
        }
    }

    closed spec fn i_lbl(pre: SystemModel::State<ConcreteProgramModel>, post: SystemModel::State<ConcreteProgramModel>, lbl: SystemModel::Label) -> (ctam_lbl: CrashTolerantAsyncMap::Label)
    {
        match lbl {
            SystemModel::Label::AcceptRequest{req} => {
                CrashTolerantAsyncMap::Label::OperateOp{
                    base_op: AsyncMap::Label::RequestOp { req }
                }
            },
            SystemModel::Label::DeliverReply{reply} => {
                CrashTolerantAsyncMap::Label::OperateOp{
                    base_op: AsyncMap::Label::ReplyOp { reply }
                }
            },
            SystemModel::Label::ProgramUIOp{op} => {
            match op {
                ProgramUserOp::Execute{req, reply} =>
                    CrashTolerantAsyncMap::Label::OperateOp{
                        base_op: AsyncMap::Label::ExecuteOp  { req, reply },
                    },
                ProgramUserOp::AcceptSyncRequest{ sync_req_id } =>
                    CrashTolerantAsyncMap::Label::ReqSyncOp{ sync_req_id },
                ProgramUserOp::DeliverSyncReply{ sync_req_id } =>
                    CrashTolerantAsyncMap::Label::ReplySyncOp{ sync_req_id },
            }},
            SystemModel::Label::ProgramDiskOp{ info } =>
                CrashTolerantAsyncMap::Label::Noop{},
            SystemModel::Label::ProgramInternal =>
                CrashTolerantAsyncMap::Label::Noop{},
            SystemModel::Label::DiskInternal => {
                if pre.sb_landed(post) {
                    CrashTolerantAsyncMap::Label::SyncOp{}
                } else {
                    CrashTolerantAsyncMap::Label::Noop{}
                }
            },
            SystemModel::Label::Crash =>
                CrashTolerantAsyncMap::Label::CrashOp{},
            SystemModel::Label::Noop =>
                CrashTolerantAsyncMap::Label::Noop{},
        }
    }

    proof fn i_lbl_valid(pre: SystemModel::State<ConcreteProgramModel>, post: SystemModel::State<ConcreteProgramModel>, lbl: SystemModel::Label, ctam_lbl: CrashTolerantAsyncMap::Label)
    {
        assert( ctam_lbl == Self::i_lbl(pre, post, lbl) );
        assert( lbl.label_correspondence(ctam_lbl) );
    }

    proof fn init_refines(pre: SystemModel::State<ConcreteProgramModel>)
    {
        assert( SystemModel::State::initialize(pre, pre.program, pre.disk) );
        assert( Self::i(pre).async_ephemeral == AsyncMap::State::init_ephemeral_state() );
        assert( Self::i(pre).sync_requests == Map::<SyncReqId,nat>::empty() );  // extn
        assert( Self::inv(pre) );

        assert( ConcreteProgramModel::is_mkfs(pre.disk) );
        broadcast use unmarshall_marshall;
        assert( CrashTolerantAsyncMap::State::initialize(Self::i(pre)) );
    }

    proof fn next_refines(pre: SystemModel::State<ConcreteProgramModel>, post: SystemModel::State<ConcreteProgramModel>, lbl: SystemModel::Label)
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

        reveal(SystemModel::State::next);
        reveal(SystemModel::State::next_by);
        let step = choose |step| SystemModel::State::next_by(pre, post, lbl, step);

        let ipre = Self::i(pre);
        let ipost = Self::i(post);
        let ilbl = Self::i_lbl(pre, post, lbl);

        match step {
            SystemModel::Step::accept_request() => {
                broadcast use insert_new_preserves_cardinality;
                let new_id = lbl->op->req.id;
                // assert(post.program.state.inv());
                // assert(post.inv());

                assume(false);
                // assert(CrashTolerantAsyncMap::State::optionally_append_version(ipre.versions, ipost.versions));

                // assert(!ipre.async_ephemeral.requests.contains(req));
                // assert(ipre.versions == ipost.versions); // true
                // assert(ipre.async_ephemeral.requests.insert(req) =~= ipost.async_ephemeral.requests);

                // assert(AsyncMap::State::next_by(iasync_pre, iasync_post, ilbl->base_op, AsyncMap::Step::request()));
                // assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, 
                //     CrashTolerantAsyncMap::Step::operate(ipost.versions, ipost.async_ephemeral)));
            }

            _ => { assume(false); }
                    /*

            SystemModel::Step::program_ui(new_program) => {
                let iasync_pre = AsyncMap::State { persistent: ipre.versions.last(), ephemeral: ipre.async_ephemeral };
                let iasync_post = AsyncMap::State { persistent: ipost.versions.last(), ephemeral: ipost.async_ephemeral };

                match lbl->op {
                    ProgramUserOp::AcceptRequest{req} => {
                       
                    },
                    ProgramUserOp::DeliverReply{reply} => {
                        assert(post.program.state.inv()) by {
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
                                KVStoreTokenized::Step::execute_transition(post.program.state.model, map_lbl));

                        pre.program.state.execute_transition_magic(post.program.state, kv_lbl, map_lbl);
                        assert(post.program.state.inv());
                        assume(post.inv()); 
                        assume(false);
        
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
                        let ctam_lbl = CrashTolerantAsyncMap::Label::ReqSyncOp{ sync_req_id };

                        // unique sync reqs promise from SystemModel
                        assert( !pre.id_history.contains(sync_req_id) );
//                         assert( forall |pr| pre.program.state.sync_requests.contains(pr)
//                                 ==> pr.0 != sync_req_id );
                        // follows from inv that ties KVStoreTokenized sync_requests to self.id_history
                        assert( !ipre.sync_requests.dom().contains(sync_req_id) );
                        let pre_set = ipre.sync_requests.dom();
                        let cur_version = (pre.program.state.model.history.len()-1) as nat;
                        let post_set = ipost.sync_requests.dom();
                        assert( post.program.state.sync_requests == pre.program.state.sync_requests.insert((sync_req_id, cur_version)) );
//                         }
                        unique_multiset_map_insert_equiv(pre.program.state.sync_requests, sync_req_id, cur_version);
                        assert( ipost.sync_requests ==
                                ipre.sync_requests.insert(sync_req_id, cur_version as nat) );

                        assume(false);

//                         assert( ipost.sync_requests ==
//                                 ipre.sync_requests.insert(sync_req_id, (ipre.versions.len() - 1) as nat) );
                        assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ctam_lbl, 
                            CrashTolerantAsyncMap::Step::req_sync()));                        
                        assert( CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl) );

                        assert forall |sync_req_pr| #![auto] post.program.state.sync_requests.contains(sync_req_pr)
                            implies post.id_history.contains(sync_req_pr.0) by {
                            if sync_req_pr.0 != sync_req_id {
                                // trigger pre inv
                                assert( pre.program.state.sync_requests.contains(sync_req_pr) );
                            }
                        }
                        assert( Self::inv(post) );
                    },
                    ProgramUserOp::DeliverSyncReply{ sync_req_id } => {
                        let pgmlbl = ProgramLabel::UserIO{op: lbl->op};
                        let kvlbl = pgmlbl.to_kv_lbl();
                        let kvstep = choose |kvstep| KVStoreTokenized::State::next_by(pre.program.state, post.program.state, kvlbl, kvstep);

                        // Dig the version (value) out of the KVStoreTokenized Step
//                         assert( kvstep is deliver_sync_reply );
                        let version:nat = kvstep.arrow_deliver_sync_reply_0();
                        assert( pre.program.state.sync_requests.contains((sync_req_id, version)) ); // trigger
                        unique_multiset_map_remove_equiv(pre.program.state.sync_requests, sync_req_id, version);
                        assume(false);
                        let ctam_lbl = CrashTolerantAsyncMap::Label::ReplySyncOp{ sync_req_id };
                        assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ctam_lbl, 
                            CrashTolerantAsyncMap::Step::reply_sync()));                        

                        assert forall |sync_req_pr| #![auto] post.program.state.sync_requests.contains(sync_req_pr)
                            implies post.id_history.contains(sync_req_pr.0) by {
                            // trigger pre inv
                            assert( pre.program.state.sync_requests.contains(sync_req_pr) );
                        }
                        assert( Self::inv(post) );
                    },
                }
                assert( Self::inv(post) );
            },
            SystemModel::Step::program_disk(new_program, new_disk) => {
                // assert(new_program == pre.program);
                assume(false);
                assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, 
                    CrashTolerantAsyncMap::Step::noop()));
                assume( Self::inv(post) );
            },
            SystemModel::Step::program_internal(new_program) => {
                assume(false);
                // assert(new_program == pre.program);
                assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, 
                    CrashTolerantAsyncMap::Step::noop()));
                assert( Self::inv(post) );
            },
            SystemModel::Step::disk_internal(new_disk) => {
                assume(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, 
                    CrashTolerantAsyncMap::Step::noop()));
                assume( Self::inv(post) );
            },
            SystemModel::Step::crash(new_program, new_disk) => {
                // This Implementation, which doesn't actually use the disk, is only "crash
                // tolerant" in the sense that it doesn't support sync. Since we never sync,
                // we maintain the invariant that the first allowed crash Version is the initial
                // state, which of course is exactly what we get when we "recover" without a disk.
                assume( false );
                assert( ipost.versions == ipre.versions.get_prefix(ipre.stable_index() + 1) ); // extn equality
                assert( ipost.async_ephemeral == AsyncMap::State::init_ephemeral_state() ); // extn equality
                assert( ipost.sync_requests == Map::<SyncReqId, nat>::empty() );    // extn equality
                assert( CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl,
                        CrashTolerantAsyncMap::Step::crash() ) );   // step witness
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
            */

        }
        assert( CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl) );
    }
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
/*

impl KVStoreTokenized::State {
    proof fn execute_transition_magic(self, post: Self, lbl: KVStoreTokenized::Label, map_lbl: MapSpec::Label)
        requires
            self.inv(), 
            Self::execute_transition(self, post, lbl, post.model, map_lbl),
        ensures 
            post.inv(),
            CrashTolerantAsyncMap::State::optionally_append_version(
                self.model.history, post.model.history),
    {
        broadcast use insert_new_preserves_cardinality;
        reveal(MapSpec::State::next);
        reveal(MapSpec::State::next_by);

        let req = lbl.arrow_ExecuteOp_req();
        let reply = lbl.arrow_ExecuteOp_reply();
        assume(false);

        KVStoreTokenized::State::execute_transition_inductive(
            self, post, lbl, post.model, map_lbl);
        assert(forall |req| #[trigger] post.requests.contains(req) 
            ==> self.requests.contains(req));
        assert(post.inv());

        let history = self.model.history;
        let post_history = post.model.history;

        if history.len() == post_history.len() {
            assert(post_history.get_prefix(history.len()) == post_history); // trigger
        } else {
            assert(post_history.get_prefix(history.len()) == history); // trigger
        }
        assert(CrashTolerantAsyncMap::State::optionally_append_version(history, post_history));
    }
}
*/
}
