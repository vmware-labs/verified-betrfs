verus!{
 

    // player 1 defines obligation in an abstract module
    // player 2 supplies ProgramModel
    // refinement of the abstract?
    // getline and putline should be here? how else does this refine?

    // PM needs a trait
    struct SystemModel<ProgramModel> {
        p: ProgramModel,
        d: DiskModel,   // we provide this
    }

    impl SystemModel<ProgramModel>  {
        spec fn curr_state(self) -> ProgramModel.State 
        // mode system => spec, proof, exec (fn)
        // exec mode inherits rust's linearity
        // spec pure functional, no linearity
        // proof ghosty but has linearity, fn vars are consumed by proof fn

        spec fn init(self) -> bool
        {
            &&& p.init()
            &&& d.init() 
        }

        proof fn next(&mut self, new_s: ProgramModel.State, in: Option<ghost_token_read>, string_out: ghost<String>) -> out: Option<ghost_token_write>
            requires 
                ProgramModel.next(self.curr_state(), new_s, ProgramModel.Label{in.string, string_out}),// to label takes care of option
            ensures 
                self.curr_state() == new_s,  // self is modified in next
                out.string == string_out,
        {

            
        }
    }

    trait ModelRefinement<ProgramModel> {

        spec fn i(s: SystemModel<ProgramModel>) -> AsyncMap.State

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



    // generalizable across any system that takes user input
    // user visible response and request
    struct UI {

        // player 2 carried out given in 

        // ghost_token can't be forged or discarded, must be consumed by state machine
        // string is the actual physical user input
        fn get_ln() -> (string, ghost_token_read)
            ensures ghost_token.string == string
        {
            // needed before we know which PSM transition is allowed?
            // we can have concurrent user requests and outstanding IOs
        }

        fn put_ln(string, ghost_token_write) 
            // requires string == ghost_token_write.string
        {
        }
    }

    // disk requests and responses
    struct Disk_IO {

    }


}