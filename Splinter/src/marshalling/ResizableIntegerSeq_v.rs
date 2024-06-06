// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
// use vstd::bytes::*;
// use vstd::slice::*;
use crate::marshalling::Slice_v::*;
use crate::marshalling::Marshalling_v::*;
use crate::marshalling::IntegerMarshalling_v::*;
use crate::marshalling::SeqMarshalling_v::*;
use crate::marshalling::UniformSizedSeq_v::*;
use crate::marshalling::ResizableUniformSizedSeq_v::*;
use crate::marshalling::math_v::*;

verus! {

// A ResizableIntegerSeqMarshalling is a specialized ResizableUniformSizedSeqMarshalling.
DISCARD THIS. We want IntegerSeqMarshallingOblinfo, which implements UniformSizedElementSeqMarshallingOblinfo.
struct <
    Int: Deepview<int> + builtin::Integer + Copy,
    IntObligations: IntObligations<Int>
> ResizableIntegerSeqMarshalling<Int, IntObligations>
{
    // low budget implementation inheritance?
    inner: 
}

} //verus!
