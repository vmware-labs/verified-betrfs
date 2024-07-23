#![verifier::loop_isolation(false)]
#![allow(non_snake_case)]   // we should probably fix up the module names to be rust-snakey

use builtin::*;
use builtin_macros::*;

pub mod marshalling;
use crate::marshalling::IntegerMarshalling_v::*;
use crate::marshalling::Marshalling_v::*;
use crate::marshalling::SeqMarshalling_v::*;
use crate::marshalling::Slice_v::*;
use crate::marshalling::UniformSizedSeq_v::*;
use crate::marshalling::ResizableUniformSizedSeq_v::*;
use vstd::string::View;
use crate::marshalling::UniformSized_v::UniformSized;
// use crate::marshalling::ResizableIntegerSeq_v::*;
use crate::marshalling::VariableSizedElementSeq_v::*;

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
    let im: IntFormat<u32> = IntFormat::new();
    //let m = IntegerSeqMarshalling{obl, eltm};
    let req = im.exec_size(&val);
    let mut data = prealloc(req);
    let end = im.exec_marshall(&val, &mut data, 0);
    (data, end)
}

exec fn u32_seq_marshaller_factory() -> (usm: UniformSizedElementSeqFormat<IntFormat<u32>>)
    ensures usm.seq_valid()
{
    let eltf: IntFormat<u32> = IntFormat::new();
    let usm = UniformSizedElementSeqFormat::new(eltf);
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
        8 <= end <= data.len(),
{
    let usm = u32_seq_marshaller_factory();
    let slice = Slice { start: 0, end };
    assume(false);  // TODO something borked in here
//     assert( 2 <= usm.length(slice@.i(data@)) ) by { assume(false); } // (nonlinear_arith);
//     assume( usm.gettable(slice@.i(data@), 1) ); // flaky!
//     assert( usm.elt_parsable(slice@.i(data@), 1) );
    usm.exec_get_elt(&slice, data, 1)
}

// fn test_index() {
//     let (data, end) = test_seq_marshalling();
//     let elt = test_seq_index(&data, end);
// }

exec fn u32_resizable_seq_marshaller_factory()
    -> (rusm: ResizableUniformSizedElementSeqMarshalling<IntFormat<u32>, u32>)
    ensures rusm.valid(), rusm.total_size == 24, rusm.seq_valid()
{
    let eltf: IntFormat<u32> = IntFormat::new();
    let lenf: IntFormat<u32> = IntFormat::new();
    let rusm = ResizableUniformSizedElementSeqMarshalling::new(eltf, lenf, 24);
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

exec fn test_resizable_seq_marshalling_append() -> (outpr: (Vec<u8>, usize))
    ensures
        outpr.0.len() == outpr.1
{
    let rusm = u32_resizable_seq_marshaller_factory();

    let mut data = prealloc(31);
    let slice: marshalling::Slice_v::Slice = Slice::all(&data);
    rusm.initialize(&slice, &mut data);
    assert( rusm.length(slice@.i(data@)) == 0 );

    let ghost v43 = (43 as u32).deepv();
    let ghost data0 = slice@.i(data@);
    assert(rusm.appendable(slice@.i(data@), v43) ) by {
        // TODO(verus): flakiness. Possibly trait related?
// NOTE: Verus failed to prove an assertion even though all of its
//           sub-assertions succeeded. This is usually unexpected, and it may
//           indicate that the proof is "flaky". It might also be a result
//           of additional expressions in the triggering context in the expanded
//           version.
        // Any single one of these sub-asserts wakes it up.
        assert( rusm.length(slice@.i(data@)) < rusm.max_length() );
//         assert( rusm.eltf.spec_size(v43) == rusm.eltf.uniform_size() );
//         assert( rusm.length(slice@.i(data@)) + 1 <= <u32 as IntFormattable>::max() );
    }
    rusm.exec_append(&slice, &mut data, &43);
    rusm.exec_append(&slice, &mut data, &8);
    rusm.exec_append(&slice, &mut data, &17);
    rusm.exec_append(&slice, &mut data, &33);
    rusm.exec_append(&slice, &mut data, &34);
//     rusm.exec_append(&slice, &mut data, &35); // fails appendable, as it should: no space left in
//     array.
    let len = data.len();
    (data, len)
}

} // verus!
  // Disturbingly this exec fn isn't verified!
fn main() {
    print!("seq_marshalling...\n");
    let (data, end) = test_seq_marshalling();
    print!("end: {:?} data {:?}\n", end, data);

    let v = test_seq_parse(&data, end);
    print!("v: {:?}\n", v);

    let elt = test_seq_index(&data, end);
    print!("elt: {:?}\n", elt);

    print!("\n");
    print!("resizable_seq_marshalling...\n");
    let (data, end) = test_resizable_seq_marshalling();
    print!("end: {:?} data {:?}\n", end, data);

    let v = test_resizable_seq_parse(&data, end);
    print!("v: {:?}\n", v);

    print!("\n");
    print!("resizable_seq_marshalling append...\n");
    let (data, end) = test_resizable_seq_marshalling_append();
    print!("end: {:?} data {:?}\n", end, data);
    let v = test_resizable_seq_parse(&data, end);
    print!("v: {:?}\n", v);
}
