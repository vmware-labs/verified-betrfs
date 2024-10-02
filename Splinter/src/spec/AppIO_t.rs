verus!{

    struct AppToken{
        // request types
        // reply types
    }

    pub fn client_request(app_request: Request) -> AppToken
    {

    }

    struct TrustedAPI {

    }

    // how application interacts with unverified clients
    impl TrustedAPI {
        // Tracked is not a spec type but a linear type that must be consumed
        pub fn receive_request(pre: Tracked<ProgramModel>) -> (req: AppRequest, post: Tracked<ProgramModel>)
            ensures pre.next(post, ProgramLabel::AcceptRequest(req))

        pub fn send_reply(reply: AppReply, pre: Tracked<ProgramModel>, post_m: Ghost<ProgramModel>) -> (post: Tracked<ProgramModel>)
            requires ProgramModel.Next(token, post_m, ProgramLabel::SendReply(reply))
            ensures post_token == post_m

    }

    pub fn verified_main(api: &TrustedAPI, pm: Tracked<ProgramModel>) 
        requires pm.init()
    {
        // single threaded model:
        // 1 program model being tracked the entire execution, handed to application
        // at receive_request, returned to client upon a reply

    }

}