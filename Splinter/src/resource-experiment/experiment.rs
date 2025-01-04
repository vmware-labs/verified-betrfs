// use builtin::*;

// use std::marker::PhantomData;
// 
use vstd::prelude::*;
// use vstd::rwlock::*;
// use std::collections::hash_map::*;
// use vstd::std_specs::hash::*;
// // use vstd::modes::*;
// use vstd::invariant::*;
// use std::sync::Arc;
// use vstd::thread::*;

mod frac;
// use crate::frac::*;

mod disk;
mod cache;

// Open questions:
// - How do we represent the disk resources being reset after a crash?
//   Who do they go back to?
// - How should I represent physical asynchrony, like disk I/O?
// - Uses of Vec<u8> should probably be [u8; 512], except we can't construct
//   those in a tracked context.
// - Disk has implementations, which is dumb. What's the proof equivalent of
//   arbitrary!() ?
//
// Generic CallBack trait experiment stalled out because I needed to pass
// executable parameters.

verus!{

fn main() {
}


}//verus!
