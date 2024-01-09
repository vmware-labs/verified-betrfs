// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use vstd::prelude::*;
use vstd::multiset::Multiset;
use crate::disk::GenericDisk_v::*;

verus! {

pub struct BranchSeq {
  pub roots: Seq<Address>
}

impl BranchSeq {
  pub open spec(checked) fn length(self) -> nat {
    self.roots.len()
  }

  pub open spec(checked) fn representation(self) -> Set<Address> {
    Set::new(|addr: Address| self.roots.contains(addr))
  }

  pub open spec(checked) fn to_multiset(self) -> Multiset<Address> {
    Multiset::from_set(self.representation())
  }

  pub open spec(checked) fn slice(self, start: nat, end: nat) -> BranchSeq
    recommends start <= end <= self.roots.len()
  {
    // Why can't verus automatically converts nat to int??
    BranchSeq{ roots: self.roots.subrange(start as int, end as int) }
  }



  // pub open spec(checked) fn length
  // pub open spec(checked) fn length
  // pub open spec(checked) fn length
  // pub open spec(checked) fn length
}



} // verus!
