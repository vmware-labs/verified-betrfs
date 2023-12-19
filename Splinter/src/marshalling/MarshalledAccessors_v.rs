// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;

verus! {

trait Config {
    spec fn valid(&self) -> bool;
}

trait Marshalling<C: Config, U> {
    spec fn parsable(cfg: &C, data: Seq<u8>) -> bool
    recommends cfg.valid()
    ;

    spec fn parse(cfg: &C, data: Seq<u8>) -> U
    recommends 
        cfg.valid(),
        Self::parsable(cfg, data)
    ;

    // Should this be slices? in verus-ironfleet, jayb used Vec<u8> + start
    fn try_parse(cfg: &C, data: &Vec<u8>) -> (ov: Option<U>)
    requires
        cfg.valid(),
    ensures
        Self::parsable(cfg, data@) <==> ov is Some,
        Self::parsable(cfg, data@) ==> ov.unwrap() == Self::parse(cfg, data@)
    ;

    spec fn marshallable(cfg: &C, value: &U) -> bool
    ;

    spec fn size(cfg: &C, value: &U) -> u64
    recommends 
        cfg.valid(),
        Self::marshallable(cfg, value)
    ;

    fn do_size(cfg: &C, value: &U) -> (sz: u64)
    requires 
        cfg.valid(),
        Self::marshallable(cfg, value),
    ensures
        sz == Self::size(cfg, value)
    ;

    fn marshall(cfg: &C, value: &U, data: &mut Vec<u8>, start: u64) -> (end: u64)
    requires 
        cfg.valid(),
        Self::marshallable(cfg, value),
        start as int + Self::size(cfg, value) as int <= old(data).len(),
    ensures
        end == start + Self::size(cfg, value),
        data.len() == old(data).len(),
        forall |i| 0 <= i < start ==> data[i] == old(data)[i],
        forall |i| end <= i < data.len() ==> data[i] == old(data)[i],
        Self::parsable(cfg, data@.subrange(start as int, end as int)),
        Self::parse(cfg, data@.subrange(start as int, end as int)) == value
    ;
}

}
