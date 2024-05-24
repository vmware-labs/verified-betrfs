#![verifier::spinoff_loop(false)]

use builtin::*;
use builtin_macros::*;

pub mod marshalling;
use crate::marshalling::IntegerMarshalling_v::*;
use crate::marshalling::Marshalling_v::*;
use crate::marshalling::SeqMarshalling_v::*;
use crate::marshalling::Slice_v::*;
use crate::marshalling::UniformSizedSeq_v::*;
use crate::marshalling::ResizableUniformSizedSeq_v::*;

// fn m<M: Marshalling<int, u32>>(m: &M) {
// }

verus! {

// What's the right design here? vec.set requires the len to be past some point; borrowed
// from the dafny design. Requiring capacity is ill-defined. Appending is senseless.
exec fn prealloc(len: usize) -> (out: Vec<u8>)
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

exec fn test_int_marshalling() -> (Vec<u8>, usize) {
    let val: u32 = 42 + 512;
    let im: IntMarshalling<u32> = IntMarshalling::new();
    //let m = IntegerSeqMarshalling{obl, eltm};
    let req = im.exec_size(&val);
    let mut data = prealloc(req);
    let end = im.exec_marshall(&val, &mut data, 0);
    (data, end)
}

exec fn u32_seq_marshaller_factory() -> UniformSizedElementSeqMarshalling<
    int,
    u32,
    IntegerSeqMarshallingOblinfo<u32, IntMarshalling<u32>>,
> {
    let intm: IntMarshalling<u32> = IntMarshalling::new();
    let oblinfo = IntegerSeqMarshallingOblinfo::new(intm);
    let eltm: IntMarshalling<u32> = IntMarshalling::new();
    let usm = UniformSizedElementSeqMarshalling::new(oblinfo, eltm);
    usm
}

exec fn test_seq_marshalling() -> (outpr: (Vec<u8>, usize))
    ensures
        outpr.0.len() == outpr.1,
        outpr.1 == 12,
{
    let mut val = Vec::new();
    val.push(42 as u32);
    val.push(7 as u32);
    val.push(16 as u32);
    let usm = u32_seq_marshaller_factory();
    assert(usm.marshallable(val.deepv()));
    let req = usm.exec_size(&val);
    let mut data = prealloc(req);
    let end = usm.exec_marshall(&val, &mut data, 0);
    (data, end)
}

exec fn test_seq_parse(data: &Vec<u8>, end: usize) -> (Vec<u32>)
    requires
        data.len() >= end,
{
    let usm = u32_seq_marshaller_factory();
    let slice = Slice { start: 0, end };
    let ovalue = usm.try_parse(&slice, data);
    // Why can't I see @ for Slice from here!?
    //     proof {
    //         let specslice = slice@;
    //         assert( usm.parsable(slice@.i(data@)) );
    //     }
    // This marshaller can't *NOT* parse any sequence of bytes.  If you give it a
    // funny end, it'll truncate the length to the nearest multiple of the uniform size.  And then
    // all the elements inside that length parse because every 4-byte sequence is a parsable u32.
    // There's a tree of predicates, but for this specialization of the Marshalling trait, we can
    // (statically) tell it always evaluates to true.
    assert(ovalue is Some);
    ovalue.unwrap()
}

exec fn test_seq_index(data: &Vec<u8>, end: usize) -> u32
    requires
        data.len() >= end >= 8,
{
    let usm = u32_seq_marshaller_factory();
    let slice = Slice { start: 0, end };
    usm.exec_get_elt(&slice, data, 1)
}

// fn test_index() {
//     let (data, end) = test_seq_marshalling();
//     let elt = test_seq_index(&data, end);
// }

exec fn u32_resizable_seq_marshaller_factory() -> (rusm: ResizableUniformSizedElementSeqMarshalling<
    int,
    u32,
    IntegerSeqMarshallingOblinfo<u32, IntMarshalling<u32>>,
    u32,
    IntMarshalling<u32>
>)
    ensures rusm.valid(), rusm.total_size == 24
{
    let intm: IntMarshalling<u32> = IntMarshalling::new();
    let oblinfo = IntegerSeqMarshallingOblinfo::new(intm);
    let eltm: IntMarshalling<u32> = IntMarshalling::new();
    let lengthm: IntMarshalling<u32> = IntMarshalling::new();
    let rusm = ResizableUniformSizedElementSeqMarshalling::new(oblinfo, eltm, 24, lengthm);
    rusm
}

exec fn test_resizable_seq_marshalling() -> (outpr: (Vec<u8>, usize))
    ensures
        outpr.0.len() == outpr.1,
        outpr.1 == 24,
{
    let mut val = Vec::new();
    val.push(42 as u32);
    val.push(7 as u32);
    val.push(16 as u32);
    let rusm = u32_resizable_seq_marshaller_factory();

    assert( val.deepv().len() == 3);    // witness to the multiplicand in marshallable
    assert( rusm.total_size == 24 );
    assert( rusm.spec_size(val.deepv()) == rusm.total_size );
    assert(rusm.marshallable(val.deepv()));
    let req = rusm.exec_size(&val);
    let mut data = prealloc(req);
    let end = rusm.exec_marshall(&val, &mut data, 0);
    (data, end)
}

exec fn test_resizable_seq_parse(data: &Vec<u8>, end: usize) -> (Option<Vec<u32>>)
    requires
        data.len() >= end,
{
    let usm = u32_resizable_seq_marshaller_factory();
    let slice = Slice { start: 0, end };
    let ovalue = usm.try_parse(&slice, data);
    ovalue
}

} // verus!
  // Disturbingly this exec fn isn't verified!
fn main() {
    let (data, end) = test_seq_marshalling();
    print!("end: {:?} data {:?}\n", end, data);

    let v = test_seq_parse(&data, end);
    print!("v: {:?}\n", v);

    let elt = test_seq_index(&data, end);
    print!("elt: {:?}\n", elt);

    let (data, end) = test_resizable_seq_marshalling();
    print!("end: {:?} data {:?}\n", end, data);

    let v = test_resizable_seq_parse(&data, end);
    print!("v: {:?}\n", v);
}
