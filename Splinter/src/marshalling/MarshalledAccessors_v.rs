// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use vstd::bytes::*;
use vstd::slice::*;

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

    fn is_parsable(cfg: &C, data: &Vec<u8>) -> (p: bool)
    requires
        cfg.valid(),
    ensures
        p == Self::parsable(cfg, data@)
    ;

    // jonh skipping translation of Parse -- does it ever save more than
    // a cheap if condition?

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

struct DefaultConfig {}

impl Config for DefaultConfig {
    spec fn valid(&self) -> bool { true }
}

struct IntegerMarshalling { }

impl Marshalling<DefaultConfig, u64> for IntegerMarshalling {

    spec fn parsable(cfg: &DefaultConfig, data: Seq<u8>) -> bool
//     recommends cfg.valid()
    {
        /*std::mem::size_of<u64>()*/
        8 <= data.len()
    }

    spec fn parse(cfg: &DefaultConfig, data: Seq<u8>) -> u64
//     recommends 
//         cfg.valid(),
//         Self::parsable(cfg, data)
    {
        spec_u64_from_le_bytes(data.subrange(0, 8))
    }

    // Should this be slices? in verus-ironfleet, jayb used Vec<u8> + start
    fn try_parse(cfg: &DefaultConfig, data: &Vec<u8>) -> (ov: Option<u64>)
//     requires
//         cfg.valid(),
//     ensures
//         Self::parsable(cfg, data@) <==> ov is Some,
//         Self::parsable(cfg, data@) ==> ov.unwrap() == Self::parse(cfg, data@)
    {
        if 8 <= data.len() {
            Some(u64_from_le_bytes(slice_subrange(data.as_slice(), 0, 8)))
        } else {
            None
        }
    }

    fn is_parsable(cfg: &DefaultConfig, data: &Vec<u8>) -> (p: bool)
//     requires
//         cfg.valid(),
//     ensures
//         p == Self::parsable(cfg, data@),
    {
        8 <= data.len()
    }

    spec fn marshallable(cfg: &DefaultConfig, value: &u64) -> bool
    {
        true
    }

    spec fn size(cfg: &DefaultConfig, value: &u64) -> u64
//     recommends 
//         cfg.valid(),
//         Self::marshallable(cfg, value)
    {
        8
    }

    fn do_size(cfg: &DefaultConfig, value: &u64) -> (sz: u64)
//     requires 
//         cfg.valid(),
//         Self::marshallable(cfg, value),
//     ensures
//         sz == Self::size(cfg, value)
    {
        8
    }

    fn marshall(cfg: &DefaultConfig, value: &u64, data: &mut Vec<u8>, start: u64) -> (end: u64)
//     requires 
//         cfg.valid(),
//         Self::marshallable(cfg, value),
//         start as int + Self::size(cfg, value) as int <= old(data).len(),
//     ensures
//         end == start + Self::size(cfg, value),
//         data.len() == old(data).len(),
//         forall |i| 0 <= i < start ==> data[i] == old(data)[i],
//         forall |i| end <= i < data.len() ==> data[i] == old(data)[i],
//         Self::parsable(cfg, data@.subrange(start as int, end as int)),
//         Self::parse(cfg, data@.subrange(start as int, end as int)) == value
    {
        // TODO this interface from verus pervasive bytes.rs can't be fast...
        let s = u64_to_le_bytes(*value);
        proof { lemma_auto_spec_u64_to_from_le_bytes(); }
        assert( s@.subrange(0, 8) =~= s@ ); // need a little extensionality? Do it by hand!

        let end = start + 8;
        let mut k:usize = 0;
        while k < 8
        invariant
            end == start + Self::size(cfg, value),
            end <= data.len(),  // manual-every-effing-invariant blows
            data.len() == old(data).len(),  // manual-every-effing-invariant blows
            s.len() == 8,  // manual-every-effing-invariant blows
            forall |i| 0 <= i < start ==> data[i] == old(data)[i],
            forall |i| 0 <= i < k ==> data[start as int + i] == s[i],
            forall |i| end <= i < data.len() ==> data[i] == old(data)[i],
        {
            //data[k] = s[k];
            // Do we want some sort of intrinsic so we don't have to copy u64s a byte at a time!?
            data.set(start as usize + k, s[k]);
            k += 1;
        }
        assert( data@.subrange(start as int, end as int) =~= s@ );  // extensionality: it's what's for ~.
        end
    }
}

}
