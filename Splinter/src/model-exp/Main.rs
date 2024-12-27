// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use crate::spec::Obligation_t;

// this is the only file that is trusted but allowed to access player 2 (untrusted) code
// because at some point we must tie the theorem and the impl together

verus!{    
    // fixed entry point provided by player 1
    fn main() {
        Impl::new().entry_point(
            AppIOPerm::new(),   // IO object, physical interface, enforce application correspondance
            Transition<Impl.ProgramModel>::new()    // ghosty transition fulfillment
        ); 
    }
}