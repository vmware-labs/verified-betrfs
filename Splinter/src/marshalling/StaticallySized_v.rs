// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

verus! {

// A type is StaticallySized if it marshals to the same number of bytes regardless of the value
// being marshalled. This trait is used to describe, for example, u32s and u64s, so that IntFormat
// can satisfy UniformSized.

pub trait StaticallySized {
    spec fn uniform_size() -> (sz: usize)
        ;

    proof fn uniform_size_ensures()
    ensures 0 < Self::uniform_size()
    ;

    exec fn exec_uniform_size() -> (sz: usize)
    ensures sz == Self::uniform_size()
    ;
}

}//verus!
