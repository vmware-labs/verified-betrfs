verus!{

pub struct AppIOPerm{

}

// Tracked (verus type) 
// TODO struct token

enum Request {
    None,
    AppRequest{req: Request},
    Sync{sync_req_id: SyncReqId},
}

enum Reply {
    None,
    AppReply{req: Reply},
    Sync{sync_req_id: SyncReqId},
}

// Use mapspec_t
impl AppIOPerm{
    fn new() -> Self
    {
        // TODO
    }

    // app get_request, corresponds to a single application level request
    // request is a physical result
    // P2 needs to advance the SM for getting request, ghost token => state in PM
    // PM level: req, execute, reply [1 to 1]

    // 
    fn get_request(self) -> (r: Request, ghost_token: Token)
        ensures r is Some ==> r == ghost_token.data
    {
        // rust physcial call
        // generating a ghost token for the data (or call into some other token generator?)
        // TODO
    }

    fn send_reply(self, r: Reply, ghost_token: Token)
        requires r == ghost_token.data
    {
        // TODO
    }

    // multiple requests can occur
    // token might not make sense
    // user  
    fn send_disk_request(self, r: DiskRequest, ghost_disk_token: Token) 
        requires r == ghost_disk_token.data
    {

    }

    fn get_disk_reply(self) -> (r: DiskReply, ghost_token: Token)
    {

    }

    // token for what happened
    // every operation provides a token

    // atomic work
    fn user_test() {

        // for a single request

        x1,y1 = AppIOPerm.get_disk_reply();
        x2,y2 = AppIOPerm.get_disk_reply();

        // computation 
        // new_s => transition in program model
        // prove that we read it 
        // y3 => map of tokens that can be sent
        

        y3 = Transition.next(s, new_s, (y1, y2)); // 
        // this advances the state of SM?

        // Read => Partial Reads => Partial Writes => Empty (clean)


        // where to enforce IO correspondence

        send_disk_request(x3, y3);
        // can we always reduce 
        
        // IO correspondence is then 

        // to enforce that write actually occurs
        // APPIOPerm tracks state 

        // LTS sharded memory op, single threaded IO 
    }
}

struct Transition<ProgramModel>{
    // phantom data
}

impl<T> Transition{
    spec fn curr_state(self) -> T.State 

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

}