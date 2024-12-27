// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
verus!{

    fn user() {
        // do read
        // compute, result
        
        assert(ProgramModel.next(self.curr_state(), new_s, ProgramModel.Label{in.string, string_out}));
    }

    struct ProgramModel{
        map: Map,
    }

    struct Program{
        map: HashMap,
    }

    impl Program{
        spec fn program_i(self) -> ProgramModel
        {
            map@ // functional view of the hash map
        }

        fn main(self) {
            self.map = HashMap::new{}; // proven => refine programmodel
            // let p = Program::Init(); 
            // let S = SystemModel<P>;
    
            put_req, ghost_read_token = get_ln();
            
            Program::next(p, p_next, put_req, resp_string);
        
            put_ln(); // for the put req
    
            get_req, ghost_read_token = get_ln();
    
            // actions here
            user(); // show the expected result in a ghosty 
            // next(self, );

        }
    }

    // implementing the trait for Program
    impl ModelRefinement<ProgramModel> for Program {
        spec fn i(s: SystemModel<ProgramModel>) -> CrashTolerantAsyncMap::State
        {
            CrashTolerantAsyncMap::State{
                versions: [s.p.map],   // optionally
                async_ephemeral: [],  // nope
                sync_requests: [],
            }
        }

        spec fn inv(s: SystemModel<ProgramModel>) -> bool

        proof fn init_refines(s: SystemModel<ProgramModel>)
            requires init(s)
            ensures inv(s)

        proof fn inv_next(s: SystemModel<ProgramModel>, s2:  SystemModel<ProgramModel>)
            requires inv(s), next(s, s2)
            ensures inv(s2) 

        
        proof fn next_refines(s: SystemModel<ProgramModel>, s2:  SystemModel<ProgramModel>)
            requires inv(s), next(s, s2), inv(s2)
            ensures AsyncMap.next(s.i(), s2.i())
    }

}