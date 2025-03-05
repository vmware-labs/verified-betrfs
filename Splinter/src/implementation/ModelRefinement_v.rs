#[allow(unused_imports)]    // lost in erasure
use builtin::*;
use vstd::prelude::*;

use vstd::{multiset::Multiset};
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

impl SystemModel::State<ConcreteProgramModel>  {
    pub open spec fn inv(self) -> bool
    {
        &&& self.program.state.wf()
        &&& self.disk.inv()

        &&& self.in_flight_request_present()
        &&& self.persistent_sb_disk_inv()

        &&& self.no_writes_till_recovery_complete() // why should a property like this be an inv?
        &&& self.at_most_one_oustanding_request_per_address()
        &&& self.responses_consistent_with_disk()

        &&& self.requests_have_unique_ids()
        &&& self.replies_have_unique_ids()
        &&& self.requests_replies_id_disjoint()

        &&& self.sync_requests_inv()
    }

    pub open spec fn in_flight_request_present(self) -> bool
    {
        &&& self.program.state.client_ready() ==> {
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
            &&& in_flight is None ==> {
                &&& forall |id| #[trigger] self.disk.requests.contains_key(id) //&& self.disk.requests[id] is WriteReq
                    ==> self.disk.requests[id].addr() != spec_superblock_addr()
                &&& forall |id| #[trigger] self.disk.responses.contains_key(id) 
                    ==> self.addr_for_id(id) != spec_superblock_addr()
            }
        }
    }

    pub open spec fn persistent_sb_disk_inv(self) -> bool
    {
        &&& self.disk.content.contains_key(spec_superblock_addr())
        &&& {
            let sb : Superblock = spec_unmarshall(self.disk.content[spec_superblock_addr()]);
            &&& sb.store.appv.invariant()
            &&& self.program.state.client_ready() ==> {
                // on disk sb either contains inflight sb or persistent sb
                let in_flight = self.program.state.in_flight;
                if in_flight is Some && self.disk.responses.contains_key(in_flight.unwrap().req_id) {
                    sb == self.program.state.in_flight_sb()
                } else {
                    sb == self.program.state.persistent_sb()
                }
            }
        }
    }

    // NOTE: 
    // pre recovery state constraint
    pub open spec fn no_writes_till_recovery_complete(self) -> bool
    {
        &&& self.program.state.recovery_state is Begin ==>
            self.disk.requests == Map::<ID, DiskRequest>::empty() && self.disk.responses == Map::<ID, DiskResponse>::empty()
        &&& self.program.state.recovery_state is AwaitingSuperblock ==> {
            &&& forall |id| #[trigger] self.disk.requests.contains_key(id) ==> !(self.disk.requests[id] is WriteReq)
            &&& forall |id| #[trigger] self.disk.responses.contains_key(id) ==> !(self.disk.responses[id] is WriteResp)
        }
    }

    pub open spec fn sync_requests_inv(self) -> bool
    {
        &&& all_elems_single(self.sync_requests)
        &&& self.program.state.client_ready() ==>   
            self.program.state.sync_req_map.dom() =~= self.sync_requests.dom()
        &&& !self.program.state.client_ready() ==> self.sync_requests.is_empty()
    }

    // TODO: update once we have structures to track id -> address
    pub open spec fn addr_for_id(self, id: ID) -> Address
    {
        spec_superblock_addr() 
    }

    // This restricts the reads we can have 
    // TODO: write responses must guarantee that the content on disk is the same as 
    pub open spec fn responses_consistent_with_disk(self) -> bool 
    {
        forall |id| #[trigger] self.disk.responses.contains_key(id)
        ==> {
            &&& self.disk.content.contains_key(self.addr_for_id(id))
            &&& self.disk.responses[id] is ReadResp /* && valid_checksum(self.disk.responses[id]->data)*/ ==>
                self.disk.responses[id]->data == self.disk.content[self.addr_for_id(id)]
            &&& self.disk.responses[id] is WriteResp ==>
                spec_marshall(self.program.state.in_flight_sb()) == self.disk.content[self.addr_for_id(id)]
        }
    }

    // for request, we only make one request at a time, losing the addr makes it hard 
    // when we only have reply and can't restrict additional requests for an addr is present in the request queue
    // right now this is fine because the only I/O is writing to superblock
    pub open spec fn at_most_one_oustanding_request_per_address(self) -> bool
    {
        // TODO: temporary restriction only valid for the simple model
        &&& forall |id| #[trigger] self.disk.requests.contains_key(id) ==>
                self.disk.requests[id].addr() == spec_superblock_addr()
    
        // no concurrent requests on the same address
        &&& forall |id1, id2| #[trigger] self.disk.requests.contains_key(id1) && #[trigger] self.disk.requests.contains_key(id2) 
            && id1 != id2 ==> self.disk.requests[id1].addr() != self.disk.requests[id2].addr()

        // no concurrent responses on the same address
        &&& forall |id1, id2| #[trigger] self.disk.responses.contains_key(id1) && #[trigger] self.disk.responses.contains_key(id2) 
            && id1 != id2 ==> self.addr_for_id(id1) != self.addr_for_id(id2)

        // no concurrent request response on the same address
        &&& forall |id1, id2| #[trigger] self.disk.requests.contains_key(id1) && #[trigger] self.disk.responses.contains_key(id2) 
            ==> self.disk.requests[id1].addr() != self.addr_for_id(id2)
    }

    pub open spec(checked) fn requests_have_unique_ids(self) -> bool 
    {
        &&& all_elems_single(self.requests)
        &&& forall |req1, req2| self.requests.contains(req1) 
            && self.requests.contains(req2)
            && req1 != req2
            ==> #[trigger] req1.id != #[trigger] req2.id
    }

    pub open spec(checked) fn replies_have_unique_ids(self) -> bool 
    {
        &&& all_elems_single(self.replies)
        &&& forall |reply1, reply2| self.replies.contains(reply1) 
            && self.replies.contains(reply2) 
            && reply1 != reply2
            ==> #[trigger] reply1.id != #[trigger] reply2.id
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
        CrashTolerantAsyncMap::State{
            versions: singleton_floating_seq(sb.version_index, sb.store.appv.kmmap),
            async_ephemeral: EphemeralState{
                requests: self.requests.dom(),
                replies: self.replies.dom(),
            },
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
         }
    }

    closed spec fn sb_landed(self: Self, post: Self) -> bool
    {
        let state = self.program.state;
        &&& state.client_ready()
        &&& state.in_flight is Some
        &&& !self.disk.responses.contains_key(state.in_flight.unwrap().req_id)
        &&& post.disk.responses.contains_key(state.in_flight.unwrap().req_id)
    }
}

pub struct RefinementProof{}

impl RefinementObligation<ConcreteProgramModel> for RefinementProof {

    open spec fn inv(model: SystemModel::State<ConcreteProgramModel>) -> bool
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
            _ => 
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
        broadcast use unmarshall_marshall;
        assert( SystemModel::State::initialize(pre, pre.program, pre.disk) );
        assert( Self::i(pre).async_ephemeral == AsyncMap::State::init_ephemeral_state() );
        assert( Self::i(pre).sync_requests == Map::<SyncReqId,nat>::empty() );  // extn
        assert( Self::inv(pre) );

        assert( ConcreteProgramModel::is_mkfs(pre.disk) );
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
        broadcast use unmarshall_marshall;
        assert( SystemModel::State::next(pre, post, lbl) );
        assert( Self::inv(pre) );

        reveal(SystemModel::State::next);
        reveal(SystemModel::State::next_by);

        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);

        broadcast use insert_new_preserves_cardinality;

        let step = choose |step| SystemModel::State::next_by(pre, post, lbl, step);

        let ipre = Self::i(pre);
        let ipost = Self::i(post);
        let ilbl = Self::i_lbl(pre, post, lbl);

        assume(false); // TODO after fixing the inv

        match step {
            SystemModel::Step::accept_request() => {
                let new_id = lbl->req.id;
                assert(post.inv()) by {
                    assert forall |req1, req2| #[trigger] post.requests.contains(req1) 
                        && #[trigger] post.requests.contains(req2) && req1 != req2
                    implies req1.id != req2.id 
                    by {
                        if req1.id == req2.id {
                            if req1.id == new_id {
                                assert(pre.requests.contains(req1) || pre.requests.contains(req2));
                            } else {
                                assert(pre.requests.contains(req1) && pre.requests.contains(req2));
                            }
                            assert(false);
                        }
                    }
                }

                assert(CrashTolerantAsyncMap::State::optionally_append_version(ipre.versions, ipost.versions));
                assert(ipre.versions == ipost.versions);

                assert(!ipre.async_ephemeral.requests.contains(lbl->req)) by {
                    if ipre.async_ephemeral.requests.contains(lbl->req) {
                        assert(pre.requests.contains(lbl->req)); // trigger
                    }
                }
                assert(ipre.async_ephemeral.requests.insert(lbl->req) =~= ipost.async_ephemeral.requests);

                let iasync_pre = AsyncMap::State { persistent: ipre.versions.last(), ephemeral: ipre.async_ephemeral };
                let iasync_post = AsyncMap::State { persistent: ipost.versions.last(), ephemeral: ipost.async_ephemeral };
                assert(AsyncMap::State::next_by(iasync_pre, iasync_post, ilbl->base_op, AsyncMap::Step::request()));
                assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, 
                    CrashTolerantAsyncMap::Step::operate(ipost.versions, ipost.async_ephemeral)));
            },
            SystemModel::Step::deliver_reply() => {
                assert(post.inv()) by {
                    assert(forall |r| #[trigger] post.replies.contains(r) ==> pre.replies.contains(r));
                }
                assert(ipre.async_ephemeral.replies.contains(lbl->reply));
                assert(!post.replies.contains(lbl->reply)) by {
                    if (post.replies.contains(lbl->reply)) {
                        assert(pre.replies.contains(lbl->reply));
                        assert(pre.replies.count(lbl->reply) > 1);
                        assert(false);
                    }
                }
                assert(ipost.async_ephemeral.replies =~= ipre.async_ephemeral.replies.remove(lbl->reply));

                let iasync_pre = AsyncMap::State { persistent: ipre.versions.last(), ephemeral: ipre.async_ephemeral };
                let iasync_post = AsyncMap::State { persistent: ipost.versions.last(), ephemeral: ipost.async_ephemeral };
                assert(AsyncMap::State::next_by(iasync_pre, iasync_post, ilbl->base_op, AsyncMap::Step::reply()));
                assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, 
                    CrashTolerantAsyncMap::Step::operate(ipost.versions, ipost.async_ephemeral)));
            },
            SystemModel::Step::program_execute(new_program) => {
                let req = lbl->op->req;
                let reply = lbl->op->reply;

                assert(AtomicState::map_transition(pre.program.state, post.program.state, req, reply));
        
                assert forall |i| #[trigger] post.program.state.history.is_active(i)
                implies post.program.state.history[i].appv.invariant()
                by {
                    if i != pre.program.state.history.len() {
                        assert(pre.program.state.history.is_active(i));
                    } else {
                        MapSpec::State::inv_next(pre.program.state.mapspec(), post.program.state.mapspec(), to_map_label(req, reply));
                        assert(post.program.state.history.last().appv.invariant());
                    }
                }

                assert(forall |req| #[trigger] post.requests.contains(req) ==> pre.requests.contains(req));
                assert(post.requests_have_unique_ids());
                assert(post.replies_have_unique_ids());

                assert(pre.in_flight_request_present());
                assert(post.in_flight_request_present()) by {
                    assert(post.program.state.in_flight == pre.program.state.in_flight);
                    assert(post.disk.requests == pre.disk.requests);
                    assert(post.disk.responses == pre.disk.responses);
                }
                assert(post.inv()); 

                assert(ipost.async_ephemeral.requests =~= ipre.async_ephemeral.requests.remove(lbl->op->req));
                assert(ipost.async_ephemeral.replies =~= ipre.async_ephemeral.replies.insert(lbl->op->reply));

                assert(CrashTolerantAsyncMap::State::optionally_append_version(ipre.versions, ipost.versions)) by {
                    if ipre.versions.len() == ipost.versions.len() {
                        assert(ipre.versions == ipost.versions);
                    } else {
                        assert(ipost.versions.get_prefix(ipre.versions.len()) == ipre.versions); // trigger
                    }
                }

                let iasync_pre = AsyncMap::State { persistent: ipre.versions.last(), ephemeral: ipre.async_ephemeral };
                let iasync_post = AsyncMap::State { persistent: ipost.versions.last(), ephemeral: ipost.async_ephemeral };
                assert(AsyncMap::State::next_by(iasync_pre, iasync_post, ilbl->base_op, AsyncMap::Step::execute(to_map_label(req, reply), iasync_post.persistent)));                        
                assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, 
                        CrashTolerantAsyncMap::Step::operate(ipost.versions, ipost.async_ephemeral)));
            },
            SystemModel::Step::program_accept_sync_request(new_program) => {
                assert(post.inv());
                assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::req_sync()));
            }
            SystemModel::Step::program_deliver_sync_reply(new_program) => {
                assert(forall |req| #[trigger] post.sync_requests.contains(req) ==> pre.sync_requests.contains(req));
                assert(post.inv());
                assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::reply_sync()));
            },
            SystemModel::Step::program_disk(new_program, new_disk) => {
                assert(ConcreteProgramModel::valid_disk_transition(pre.program, post.program, lbl->info));
                let reqs = lbl->info.reqs;
                let resps = lbl->info.resps;
                let disk_event = choose |disk_event| AtomicState::disk_transition(
                    pre.program.state, post.program.state, disk_event, reqs, resps);

                let disk_lbl = DiskLabel::DiskOps{
                    requests: multiset_to_map(reqs),
                    responses: multiset_to_map(resps),
                };

                assert(disk_lbl->responses <= pre.disk.responses);
                assert(disk_lbl->requests <= post.disk.requests);

                match disk_event {
                    DiskEvent::InitiateRecovery{req_id} => {
                        assert(AtomicState::initiate_recovery(pre.program.state, post.program.state, reqs, resps, req_id));
                        assert(post.program.state.wf());
                        multiset_map_singleton_ensures(req_id, DiskRequest::ReadReq{from: spec_superblock_addr()});
                    },
                    DiskEvent::CompleteRecovery{req_id, raw_page} => {
                        assert(AtomicState::complete_recovery(pre.program.state, post.program.state, reqs, resps, req_id, raw_page));
                        assert(AsyncDisk::State::disk_ops(pre.disk, post.disk, disk_lbl));
                        multiset_map_membership(resps, req_id, DiskResponse::ReadResp{data: raw_page});
                        assert(disk_lbl->responses == map!{req_id => DiskResponse::ReadResp{data: raw_page}});

                        assert(disk_lbl->responses.contains_key(req_id)); // trigger
                        assert(pre.disk.responses.contains_key(req_id));
                        assert(raw_page == pre.disk.content[spec_superblock_addr()]);

                        let superblock = spec_unmarshall(raw_page); 
                        assert(superblock.store.appv.invariant());
                        assert(post.program.state.wf());
                        assert(post.sync_requests_inv());
                    },
                    DiskEvent::ExecuteSyncBegin{req_id} => {    
                        AtomicState::execute_sync_begin(pre.program.state, post.program.state, reqs, resps, req_id);
                        let sb = pre.program.state.ephemeral_sb();
                        let write_req = DiskRequest::WriteReq{to: spec_superblock_addr(), data: spec_marshall(sb)};
                        multiset_map_membership(reqs, req_id, write_req);
                    },
                    DiskEvent::ExecuteSyncEnd{} => {
                        AtomicState::execute_sync_end(pre.program.state, post.program.state, reqs, resps);
                        let info = pre.program.state.in_flight.unwrap();
                        multiset_map_membership(resps, info.req_id, DiskResponse::WriteResp{});

                        assert(forall |i| #[trigger] post.program.state.history.is_active(i) 
                            ==> pre.program.state.history.is_active(i)); // trigger
                        assert(post.program.state.wf());
                    }
                }
                assert(post.inv());
                assert(ipre == ipost);
                assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
            },
            SystemModel::Step::program_internal(new_program) => {
                assert(ipre == ipost);
                assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
            },
            SystemModel::Step::disk_internal(new_disk) => {
                if pre.sb_landed(post) {
                    assert(post.inv());
                    let info = pre.program.state.in_flight.unwrap();
                    assert(ipre.stable_index() <= info.version < ipre.versions.len());
                    assert(ipost.versions == ipre.versions.get_suffix(info.version as int));
                    assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::sync(info.version as int)));
                } else {
                    assert(post.inv());
                    assert(ipre == ipost);
                    assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
                }
            },
            SystemModel::Step::crash(new_program, new_disk) => {
                assert(post.inv());
                assert(ipre.versions.get_prefix(ipre.stable_index()+1) == ipost.versions); 
                assert(ipost.async_ephemeral == AsyncMap::State::init_ephemeral_state()); // ext_eq
                assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::crash()));
            },
            SystemModel::Step::noop() => {
                assert(ipre == ipost);
                assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
            },
            _ => { assert(false); }
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
}
