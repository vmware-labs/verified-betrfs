#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
// use crate::pervasive::{*,seq::*};


// Does verus have imaps? Yes, Maps includes infinite maps 
// https://verus-lang.github.io/verus/guide/spec_lib.html

verus!{

    // datatype V = V();   // todo: Rust only has struct and enum types

// TODO(tony): Is generics the right way to do this? Nope
pub spec fn terminal_value<V>(v: V) -> bool;


fn main() {}
}
