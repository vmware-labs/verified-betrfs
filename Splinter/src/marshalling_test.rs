#![verifier::spinoff_loop(false)]

use builtin::*;
use builtin_macros::*;

pub mod marshalling;
use crate::marshalling::IntegerMarshalling_v::*;
use crate::marshalling::Marshalling_v::*;
use crate::marshalling::SeqMarshalling_v::*;
use crate::marshalling::UniformSizedSeq_v::*;

// fn m<M: Marshalling<int, u32>>(m: &M) {
// }

verus! {

// What's the right design here? vec.set requires the len to be past some point; borrowed
// from the dafny design. Requiring capacity is ill-defined. Appending is senseless.
fn prealloc(len: usize) -> (out: Vec<u8>)
    ensures
        out.len() == len,
{
    let mut out = Vec::new();
    let mut i = 0;
    while i < len
        invariant
            i <= len,
            out.len() == i,
    {
        out.push(0);
        i += 1;
    }
    out
}

fn test_int_marshalling() -> (Vec<u8>, usize) {
    let val: u32 = 42 + 512;
    let im: IntMarshalling<u32> = IntMarshalling::new();
    //let m = IntegerSeqMarshalling{obl, eltm};
    let req = im.exec_size(&val);
    let mut data = prealloc(req);
    let end = im.exec_marshall(&val, &mut data, 0);
    (data, end)
}

fn test_seq_marshalling() -> (Vec<u8>, usize) {
    let mut val = Vec::new();
    val.push(42 as u32);
    val.push(7 as u32);
    val.push(16 as u32);
    let lengthm: IntMarshalling<u32> = IntMarshalling::new();
    let oblinfo = IntegerSeqMarshallingOblinfo::new(lengthm);
    let eltm: IntMarshalling<u32> = IntMarshalling::new();
    let usm = UniformSizedElementSeqMarshalling::new(oblinfo, eltm);

    assert( usm.marshallable(val.deepv()) );
    let req = usm.exec_size(&val);
    let mut data = prealloc(req);
    let end = usm.exec_marshall(&val, &mut data, 0);
    (data, end)
}

} // verus!
fn main() {
    let (v, end) = test_seq_marshalling();
    print!("end: {:?} v {:?}\n", end, v);
}
