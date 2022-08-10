#![allow(unused_imports)]

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

// TODO(jonh): `error: state machine field must be marked public`: why make me type 'pub', then?
// It's our syntax!

state_machine!{ AsyncMap {
    fields { pub persistent: PersistentState, pub ephemeral: EphemeralState }
}}

//}

fn main() { }
