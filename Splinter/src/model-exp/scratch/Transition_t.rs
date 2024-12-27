// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
verus!{
    enum State {
        Ready,
        Reading,
        Writing,
    }

    struct Perm{

    }

    // one instance per transition
    impl Perm{
        spec fn state(self) -> State

        spec fn app_read_set(self) -> Set<ID> //??

        spec fn io_read_set(self) -> Set<ID> //??

        fn get_request(&mut self) -> (r: Request)
            requires 
                self.state() is Ready || self.state() is Reading
            ensures 
                self.state() is Reading,
                self.app_read_set() == old(self).app_read_set() + [r]
        { 
            // rust physcial call
            // generating a ghost token for the data (or call into some other token generator?)
            // TODO
        }

        fn get_disk_reply(&mut self) -> (r: DiskReply)
            requires 
                self.state() is Ready || self.state() is Reading
            ensures 
                self.state() is Reading,
                self.io_read_set() == old(self).io_read_set() + [r]
        {

        }
        
        // application IO
        // sequence of input output 
        // multithreaded case app IO 

        // Player 1: LTS to Single threaded linearization point

        spec fn curr_state(self) -> T.State 

        // tracked by state 
        proof fn next(&mut self, new_s: ProgramModel.State, diskout: Set<IO>, appout: ID)
            requires 
                self.state() is Ready || self.state() is Reading
                ProgramModel.next(self.curr_state(), new_s, ProgramModel.Label{self.io_read_set(), diskout, self.app_read_set(), appout}),
            ensures 
                self.state() is Writing,
                self.curr_state() == new_s,  // self is modified in next
                self.io_write_set() == diskout,
                self.app_write_set() == appout,
        {
        }    

        fn send_reply(self, r: Reply)
            requires 
                self.app_write_set().contains(r)
            ensures 
                self.app_write_set() == old(self).app_write_set() - [r]
        {
            // TODO
        }

        fn send_disk_request(self, r: DiskRequest) 
            requires 
                self.io_write_set().contains(r)
            ensures 
                self.io_write_set() == old(self).io_write_set() - [r]
        {

        }

        proof fn done(&mut self)
            requires 
                self.state() is Writing,
                self.io_write_set() == empty(),
                self.app_write_set() == empty()
            ensures  
                self.state() is Ready,
        {

        }
}
}