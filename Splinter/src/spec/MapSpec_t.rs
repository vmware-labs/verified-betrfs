#![allow(unused_imports)]

// TODO _t and _s enforcement in the build system? Gasp, don't know how to thing about
// approaching/modifying/enhancing crate build...?

use builtin_macros::*;
use builtin::*;
use crate::pervasive::{*,map::*,set::*};

use crate::spec::FloatingSeq_t::*;

use state_machines_macros::state_machine;

verus! {

// TODO jonh is sad that he can't namespace-scope these definitions inside a state machine.
// Maybe there's some other scoping tool I should be using?
type Key = int;
type Value = int;
pub type TotalKMMap = Map<Key, Value>;

// TODO(jonh): Need to genericize the types of Key, Value; and then we'll need to axiomitify /
// leave-unspecified a default value
pub open spec fn default_value() -> Value {
    0
}

pub open spec fn total_default_kmmap() -> TotalKMMap
{
    Map::total(|k| default_value())
}

#[is_variant]
pub enum Input {
    GetInput{key: Key},
    PutInput{key: Key, value: Value},
    NoopInput
}

#[is_variant]
pub enum Output {
    GetOutput{value: Value},
    PutOutput,
    NoopOutput
}

    // TODO ugly workaround for init!{my_init()} being a predicate from outside
    // TODO 2: can't declare this fn inside MapSpec state_machine!?
    pub open spec fn my_init() -> MapSpec::State
    {
        MapSpec::State{ kmmap: total_default_kmmap() }
    }

state_machine!{ MapSpec {
    fields { pub kmmap: TotalKMMap }

    init!{
        my_init_2() {
            init kmmap = my_init().kmmap;
    }}

    transition!{
        query(input: Input, output: Output) {
            require input.is_GetInput();
            require output.is_GetOutput();
            // require let GetInput(key) =  // TODO how?

            require let Input::GetInput { key } = input;
            require let Output::GetOutput { value } = output;
//            let key = input.get_GetInput_key();  // TODO eeeew
//            let value = input.get_GetInput_value();
            require pre.kmmap[key] == value;
    }}

    transition!{
        put(key: Key, value: Value) {
            update kmmap = pre.kmmap.insert(key, value);
    }}
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

#[is_variant]
pub enum AsyncUILabel { // Was AsyncMod.UIOp
    RequestOp {req: Request},
    ExecuteOp {req: Request, reply: Reply},
    ReplyOp {reply: Reply},
}

// CrashTolerantMod things
type SyncReqId = nat;
type Version = PersistentState;

// TODO(jonh): `error: state machine field must be marked public`: why make me type 'pub', then?
// It's our syntax!

state_machine!{ AsyncMap {
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

    transition!{ do_request(req: Request) {
        require !pre.ephemeral.requests.contains(req);
        // TODO(travis): Wanted to type set![req], but `macro not allowed in transition expression`
        update ephemeral = EphemeralState { requests: pre.ephemeral.requests.insert(req), ..pre.ephemeral };
    } }

    transition!{ do_execute(req: Request, reply: Reply) {
        
    } }

    transition!{ do_reply(reply: Reply) {
        require pre.ephemeral.replies.contains(reply);
        update ephemeral = EphemeralState { replies: pre.ephemeral.replies.remove(reply), ..pre.ephemeral };
    } }
} }

// TODO(jonh): was sad to concretize Map (because no module functors). Is there a traity alternative?
// TODO(jonh): also sad to cram Async into CrashTolerant (because Async wasn't really a real state machine).
// How do we feel about going slightly off the state machine rails and having it fall apart?
state_machine!{ CrashTolerantAsyncMap {
    fields {
        pub versions: FloatingSeq<Version>,
        pub async_ephemeral: EphemeralState,
        pub sync_requests: Map<SyncReqId, nat>,
    }

//    #[invariant]
//  TODO(jonh): Unhappy that the invariant (proof work) is in the same file as the model
    pub open spec fn the_inv(self) -> bool {
        &&& 0 < self.versions.len()
        &&& self.versions.is_active(self.versions.len() - 1)
    }

    pub open spec fn stable_index(self) -> int {
        self.versions.first_active_index()
    }

    // TODO(travis): init!{} with no body produces confusing error message
    init!{ Init() {
        // Translate InitState?
        // TODO eeww we had to propagate predicate style up to here, and it's getting gross, all
        // because MapSpec::State::my_init was a predicate.
        init versions = floating_seq(0, 1, |i| AsyncMap::State::init_persistent_state());
        init async_ephemeral = AsyncMap::State::init_ephemeral_state();
        init sync_requests = Map::empty();
    } }

    pub open spec fn optionally_append_version(versions: FloatingSeq<Version>, versions_prime: FloatingSeq<Version>) -> bool
    {
      // new versions list is either some new thing appended to the old one,
      ||| (0<versions_prime.len() && versions_prime.drop_last() === versions)
      // or unchanged. We allow unchanged in the trusted spec so that
      // implementations don't have to account for number of read-only (query) ops.
      ||| versions_prime === versions
    }
    
    transition!{
        operate(op: AsyncUILabel, new_versions: FloatingSeq<Version>, new_async_ephemeral: EphemeralState, async_step: AsyncMap::Step) {
            // want to introduce nondeterminism for new_versions, then write a predicate saying
            // which values are okay
            require State::optionally_append_version(pre.versions, new_versions);
            // What's the syntax for (a) consing up an AsyncMap object and (b) calling its implicit Next
            // predicate?
            require AsyncMap::State::next_by(
                AsyncMap::State { persistent: pre.versions.last(), ephemeral: pre.async_ephemeral },
                AsyncMap::State { persistent: new_versions.last(), ephemeral: new_async_ephemeral },
                async_step);

            update versions = new_versions;
            update async_ephemeral = new_async_ephemeral;
    } }

    transition!{
        crash() {
            update versions = pre.versions.get_prefix(pre.stable_index() + 1);
            update async_ephemeral = AsyncMap::State::init_ephemeral_state();
            update sync_requests = Map::empty();
        }
    }

    transition!{
        sync(new_stable_index: int) {
            require pre.stable_index() <= new_stable_index < pre.versions.len();
            update versions = pre.versions.get_suffix(new_stable_index);
        }
    }
    
    transition!{
        req_sync(sync_req_id: SyncReqId) {
            // TODO (tony): add Maps::contains to Pervasives
            require pre.sync_requests.dom().contains(sync_req_id);
            require pre.sync_requests[sync_req_id] <= pre.stable_index();
            update sync_requests = pre.sync_requests.remove(sync_req_id);
        }
    }

    // TODO: jonh is sad that I can't put this invariant & proof elsewhere. We separate
    // our state machine definitions from our invariant & refinement proof text.
//    #[inductive(operate)]
//    fn operate_inductive(pre: Self, post: Self, op: AsyncUILabel) { }
    

}}

}

fn main() { }
