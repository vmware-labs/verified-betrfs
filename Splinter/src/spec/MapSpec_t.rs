#![allow(unused_imports)]

// TODO _t and _s enforcement in the build system? Gasp, don't know how to thing about
// approaching/modifying/enhancing crate build...?

use builtin_macros::*;
use builtin::*;
use crate::pervasive::{*,map::*,set::*};

use crate::spec::Messages_t::*;
use crate::spec::FloatingSeq_t::*;
use crate::spec::TotalKMMap_t::*;

use state_machines_macros::state_machine;

// TODO (tenzin): break out everything in this file into separate files/modules
// (cleaner logical breaks)
verus! {

#[is_variant]
pub enum Input {
    QueryInput{key: Key},
    PutInput{key: Key, value: Value},
    NoopInput
}

#[is_variant]
pub enum Output {
    QueryOutput{value: Value},
    PutOutput,
    NoopOutput
}

// TODO ugly workaround for init!{my_init()} being a predicate from outside
// TODO 2: can't declare this fn inside MapSpec state_machine!?
pub open spec fn my_init() -> MapSpec::State
{
    MapSpec::State{ kmmap: empty_total_map() }
}

// TODO (jonh): Make this automated. A macro of some sort
pub open spec fn getInput(label: MapSpec::Label) -> Input {
    match label {
        MapSpec::Label::Query{input, output} => input,
        MapSpec::Label::Put{input, output} => input,
        MapSpec::Label::Noop{input, output} => input,
    }
}

pub open spec fn getOutput(label: MapSpec::Label) -> Output {
    match label {
        MapSpec::Label::Query{input, output} => output,
        MapSpec::Label::Put{input, output} => output,
        MapSpec::Label::Noop{input, output} => output,
    }
}

state_machine!{ MapSpec {
    fields { pub kmmap: TotalKMMap }

    #[is_variant]
    pub enum Label{
        Query{input: Input, output: Output},
        Put{input: Input, output: Output},
        Noop{input: Input, output: Output},
    }

    init!{
        // TODO: examine this weird nesting predicate stuff later
        // Core issue seems to be wanting to know the concrete initial
        // state outside of this state machine
        my_init_2() {
            init kmmap = my_init().kmmap;
        }
    }

    transition!{
        query(label: Label) {
            require let Label::Query{input, output} = label;

            require let Input::QueryInput { key } = input;
            require let Output::QueryOutput { value } = output;

            require pre.kmmap[key].get_Define_value() == value;  
        }
    }

    transition!{
        put(label: Label) {
            require let Label::Put{input, output} = label;

            require let Input::PutInput { key, value } = input;
            require let Output::PutOutput = output;

            update kmmap = pre.kmmap.insert(key, Message::Define{value});
        }
    }

    transition!{
        noop(label: Label) {
            require let Label::Noop{input, output} = label;

            require let Input::NoopInput = input;
            require let Output::NoopOutput = output;
        }
    }
}}

// Async things
type ID = int;  // wishing for genericity
pub struct Request {
    pub input: Input,
    pub id: ID
}
pub struct Reply {
    pub output: Output,
    pub id: ID
}
pub struct PersistentState {
    pub appv: MapSpec::State
}
pub struct EphemeralState {
    pub requests: Set<Request>,
    pub replies: Set<Reply>,
}

// TODO(jonh): `error: state machine field must be marked public`: why make me type 'pub', then?
// It's our syntax!

state_machine!{ AsyncMap {
    #[is_variant]
    pub enum Label { // Was AsyncMod.UIOp
        RequestOp { req: Request },
        ExecuteOp { req: Request, reply: Reply },
        ReplyOp { reply: Reply },
    }

    pub open spec fn init_persistent_state() -> PersistentState {
        PersistentState { appv: my_init() }
    }

    pub open spec fn init_ephemeral_state() -> EphemeralState {
        EphemeralState{ requests: Set::empty(), replies: Set::empty() }
    }

    fields {
        pub persistent: PersistentState,
        pub ephemeral: EphemeralState,
    }

    transition!{ request(label: Label) {
        require let Label::RequestOp{ req } = label;
        require !pre.ephemeral.requests.contains(req);
        update ephemeral = EphemeralState { requests: pre.ephemeral.requests.insert(req), ..pre.ephemeral };
    } }

    transition!{ execute(label: Label, map_label: MapSpec::Label, post_persistent: PersistentState) {
        require let Label::ExecuteOp{ req, reply } = label;
        require req.id == reply.id;
        require pre.ephemeral.requests.contains(req);
        // Avoid collapsing replies together
        require !pre.ephemeral.replies.contains(reply);

        // TODO(jonh): Calling into a contained state machine is painful and long
        require getInput(map_label) == req.input;
        require getOutput(map_label) == reply.output;
        require MapSpec::State::next(
            pre.persistent.appv,
            post_persistent.appv,
            map_label
        );
        update persistent = post_persistent;

        update ephemeral = EphemeralState{
            requests: pre.ephemeral.requests.remove(req),
            replies: pre.ephemeral.replies.insert(reply),
        };
    } }

    transition!{ reply(label: Label) {
        require let Label::ReplyOp{ reply } = label;
        require pre.ephemeral.replies.contains(reply);
        update ephemeral = EphemeralState { replies: pre.ephemeral.replies.remove(reply), ..pre.ephemeral };
    } }
} }

type SyncReqId = nat;
pub type Version = PersistentState;

// TODO(jonh): was sad to concretize Map (because no module functors). Is there a traity alternative?
// TODO(jonh): also sad to cram Async into CrashTolerant (because Async wasn't really a real state machine).
// How do we feel about going slightly off the state machine rails and having it fall apart?
state_machine!{ CrashTolerantAsyncMap {
    fields {
        pub versions: FloatingSeq<Version>,
        pub async_ephemeral: EphemeralState,
        pub sync_requests: Map<SyncReqId, nat>,
    }

    #[is_variant]
    pub enum Label { // Unrolled version of Dafny labels for CrashTolerantMod(MapSpecMod)
        OperateOp{ base_op: AsyncMap::Label },
        CrashOp,
        SyncOp,
        ReqSyncOp{ sync_req_id: SyncReqId },
        ReplySyncOp{ sync_req_id: SyncReqId },
        Noop,
    }
    // TODO: complete this state machine

    pub open spec fn stable_index(self) -> int {
        self.versions.first_active_index()
    }

    // TODO(travis): init!{} with no body produces confusing error message
    init!{ initialize() {
        init versions = FloatingSeq::new(0, 1, |i| AsyncMap::State::init_persistent_state());
        init async_ephemeral = AsyncMap::State::init_ephemeral_state();
        init sync_requests = Map::empty();
    } }

    pub open spec fn optionally_append_version(versions: FloatingSeq<Version>, versions_prime: FloatingSeq<Version>) -> bool
    {
      // new versions list is either some new thing appended to the old one,
      ||| (0 < versions_prime.len() && versions_prime.drop_last() == versions)
      // or unchanged. We allow unchanged in the trusted spec so that
      // implementations don't have to account for number of read-only (query) ops.
      ||| versions_prime == versions
    }
    
    transition!{
        operate(
            label: Label,
            new_versions: FloatingSeq<Version>,
            new_async_ephemeral: EphemeralState)
        {
            // TODO: add label checking boilerplate
            require let Label::OperateOp{ base_op } = label;

            // want to introduce nondeterminism for new_versions, then write a predicate saying
            // which values are okay
            require State::optionally_append_version(pre.versions, new_versions);
            // What's the syntax for (a) consing up an AsyncMap object and (b) calling its implicit Next
            // predicate?
            require AsyncMap::State::next(
                AsyncMap::State { persistent: pre.versions.last(), ephemeral: pre.async_ephemeral },
                AsyncMap::State { persistent: new_versions.last(), ephemeral: new_async_ephemeral },
                base_op
            );

            update versions = new_versions;
            update async_ephemeral = new_async_ephemeral;
    } }

    transition!{
        crash(label: Label) {
            require let Label::CrashOp = label;

            update versions = pre.versions.get_prefix(pre.stable_index() + 1);
            update async_ephemeral = AsyncMap::State::init_ephemeral_state();
            update sync_requests = Map::empty();
        }
    }

    transition!{
        sync(label: Label, new_stable_index: int) {
            require let Label::SyncOp = label;

            require pre.stable_index() <= new_stable_index < pre.versions.len();
            update versions = pre.versions.get_suffix(new_stable_index);
        }
    }
    
    transition!{
        req_sync(label: Label) {
            require let Label::ReqSyncOp{ sync_req_id } = label;

            // TODO (tony): add Maps::contains to Pervasives
            require !pre.sync_requests.dom().contains(sync_req_id);
            update sync_requests =
                pre.sync_requests.insert(sync_req_id, (pre.versions.len() - 1) as nat);
        }
    }

    transition!{
        reply_sync(label: Label) {
            require let Label::ReplySyncOp{ sync_req_id } = label;

            // TODO (tony): add Maps::contains to Pervasives
            require pre.sync_requests.dom().contains(sync_req_id);

            require pre.sync_requests[sync_req_id] <= pre.stable_index();
            update sync_requests = pre.sync_requests.remove(sync_req_id);
        }
    }

    transition!{
        noop(label: Label) {
            require let Label::Noop = label;
        }
    }

    //  TODO(jonh): Unhappy that the invariant (proof work) is in the same file as the model
    #[invariant]
    pub open spec fn the_inv(self) -> bool {
        &&& 0 < self.versions.len()
        &&& self.versions.is_active(self.versions.len() - 1)
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }
   
    #[inductive(operate)]
    fn operate_inductive(pre: Self, post: Self, label: Label, new_versions: FloatingSeq<Version>, new_async_ephemeral: EphemeralState) { }
   
    #[inductive(crash)]
    fn crash_inductive(pre: Self, post: Self, label: Label) { }
   
    #[inductive(sync)]
    fn sync_inductive(pre: Self, post: Self, label: Label, new_stable_index: int) { }
   
    #[inductive(req_sync)]
    fn req_sync_inductive(pre: Self, post: Self, label: Label) { }
   
    #[inductive(reply_sync)]
    fn reply_sync_inductive(pre: Self, post: Self, label: Label) { }
   
    #[inductive(noop)]
    fn noop_inductive(pre: Self, post: Self, label: Label) { }

    // TODO: jonh is sad that I can't put this invariant & proof elsewhere. We separate
    // our state machine definitions from our invariant & refinement proof text.
//    #[inductive(operate)]
//    fn operate_inductive(pre: Self, post: Self, op: AsyncUILabel) { }
}}

}

fn main() { }
