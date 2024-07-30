// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use builtin::*;
use vstd::prelude::*;
use vstd::{map::*,multiset::*};
use crate::disk::GenericDisk_v::*;

verus!{
    pub type Likes = Multiset<Address>;

    pub open spec(checked) fn no_likes() -> Likes
    {
        Multiset::empty()
    }

    // pub open spec(checked) fn map_sum<T>(s: Map<T, Likes>) -> Likes
    //     decreases s.dom().len() when s.dom().finite()
    // {
    //     if s.dom().len() == 0 {
    //         no_likes()
    //     } else {
    //         // TODO(verus): natural but fails due to lack of axiom support
    //         // let k = choose |k| s.dom().contains(k); 
    //         let k = s.dom().choose();
    //         map_sum(s.remove(k)).add(s[k])
    //     }
    // }
}
