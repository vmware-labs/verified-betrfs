#![allow(unused_imports)]

// TODO _t and _s enforcement in the build system? Gasp, don't know how to thing about
// approaching/modifying/enhancing crate build...?

use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::*;
// TODO Why doesn't pervasive::* let us see Map, Set?
use pervasive::map::*;
use pervasive::set::*;

use state_machines_macros::state_machine;

//verus! {

// TODO jonh is sad that he can't namespace-scope these definitions inside a state machine.
// Maybe there's some other scoping tool I should be using?
type Key = int;
type Value = int;
type TotalKMMap = Map<Key, Value>;

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

state_machine!{ MapSpec {
    fields { pub kmmap: TotalKMMap }

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
        }
    }

    transition!{
        put(key: Key, value: Value) {
            update kmmap = pre.kmmap.insert(key, value);
        }

    }
}}

// Async things
type ID = int;  // wishing for genericity
struct Request {
    input: Input,
    id: ID
}
struct Reply {
    output: Output,
    id: ID
}
pub struct PersistentState {
    appv: MapSpec::State
}
pub struct EphemeralState {
    requests: Set<Request>,
    replies: Set<Reply>,
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

// TODO(jonh): was sad to concretize Map (because no module funcors), and
// sad to cram Async into CrashTolerant (because Async wasn't really a real state machine)
state_machine!{ CrashTolerantAsyncMap {
    fields {
        pub versions: FloatingSeq<Version>,
        pub asyncEphemral: EphemeralState,
        pub syncRequests: Map<SyncReqId, nat>,
    }

//    #[invariant]
    pub fn the_inv(self) -> bool {
        &&& 0 < self.versions.length()
        &&& self.versions.IsActive(self.versions.length() - 1)
    }

    fn StableIndex(self) -> nat {
        self.versions.FirstActiveIndex()
    }

    transition!{
        operate(op: AsyncUILabel) {
        }
    }

    // TODO: jonh is sad that I can't put this invariant & proof elsewhere. We separate
    // our state machine definitions from our invariant & refinement proof text.
    #[inductive(operate)]
    fn operate_inductive(pre: Self, post: Self, op: AsyncUILabel) { }
    

}}

//}

fn main() { }
