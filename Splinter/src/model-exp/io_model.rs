// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
verus!{
    // delayed response refines to the one that write writes as it is permitted
    // received requests & crash before taking the transition

    // iteration
    state_machine!{ RealModel{ // Chunky Model

        fields {
            // s: SystemModel<AsyncStateMachine>, // chunky program, with disk

            p: ChunkyProgramModel,
            d: DiskModel,

            pending_app_request: Map<ID, AppRequest>,
            io_replies: Map<ID, DiskReply>,
            pending_app_replies,
            io_requests,
        }

        enum Label {
            ReceiveApp{new_request},
            ReplyApp{},
            Internal{app_requests, io_replies, io_requests, app_replies},
            ReceiveIO{},
            RequestIO{},
            Crash{},    
        }

        transition!{
            crash(lbl){
                require lbl is Crash;
                require p.next(new_p, Crash);
                require d.next(new_d, Crash);

                update pending_app_request = Map::empty();
                update io_replies = Map::empty();
                update pending_app_replies = Map::empty();
                update io_requests = Map::empty();

                update p = new_p;
                update d = new_d;

            }
        }

        transition!{
            // received a physical input, update read tokens 
            get_app_input(lbl) {
                require lbl is ReceiveApp;
                update pending_app_request = pending_app_request.insert(lbl->new_request);
            }
        }

        transition!{
            // recieved the actual disk reply, update read tokens
            get_io_reply(lbl) {
                require lbl is ReceiveIO;
                require d.next(new_d, lbl->new_reply);
                update io_replies = io_replies.insert(lbl->new_reply);
                update d = new_d; // disk sent the replies
            }
        }

        // how is it permitted to generate IO request??? separate transition

        transition!{
            // consumes read tokens, generate token for allowed writes or reads?
            // maybe tokens should be further split into allowing reads on any block and writes only when transition permitts
            ghost_program_transition(lbl) {
                require lbl is Internal;
                require app_request <= pre.pending_app_request;
                require io_replies <= pre.io_replies;

                // app_request determines the transition
                require p.next(new_s, lbl->app_request, lbl->io_replies, lbl->io_requests, lbl->app_replies);

                update pending_app_request = pre.pending_app_request.remove(app_request);
                update io_replies = pre.io_replies.remove(io_replies);
                update pending_app_replies += lbl->app_replies;
                update io_requests += lbl->io_requests;
                update p = new_p;
            }
        }

        transition!{
            // consumes an app token to reply, concrete delayed reply behavior
            send_app_output(lbl) {
                require lbl is ReplyApp;
                update pending_app_reply = pending_app_reply.remove(lbl->new_reply);
            }
        }

        transition!{
            // consumes a token to request disk op
            disk_internal(lbl) {
                require lbl is DiskInternal;
                require d.next(new_d, Internal);
                update d = new_d;
            }
        }
        
        transition!{
            // consumes a token to request disk op
            send_disk_request(lbl) {
                require lbl is RequestIO;
                require d.next(new_d, lbl->io_request);
                update io_requests = io_requests.remove(lbl->new_request);
                update d = new_d;
            }
        }

        // theorem: every execution of the async reply/request is equivalent to an execution 
        // where every step is atomic simulation argument
    }
    }


    // iteration
    state_machine!{ Atomic{
            fields {
                s: SystemModel<AsyncStateMachine>,
    
                // pending_app_request: Map<ID, AppRequest>,
                // io_replies: Map<ID, DiskReply>,
                // pending_app_replies,
                // io_requests,
            }
    
            enum Label {
                ReceiveApp{new_request},
                ReplyApp{},
                Internal{app_requests, io_replies, io_requests, app_replies},
                ReceiveIO{},
                ReplyIO{},
                Crash{},    
            }
    
            transition!{
                crash(lbl, new_s){
                    require lbl is Crash;
                    require s.next(new_s, Crash);
    
                    update pending_app_request = Map::empty();
                    update io_replies = Map::empty();
                    update pending_app_replies = Map::empty();
                    update io_requests = Map::empty();
    
                    update s = new_s;
                }
            }
    
            transition!{
                get_app_input(lbl) {
                    require lbl is ReceiveApp;
                    update pending_app_request = pending_app_request.insert(lbl->new_request);
                }
            }
    
            transition!{
                get_io_reply(lbl) {
                    require lbl is ReceiveIO;
                    update io_replies = io_replies.insert(lbl->new_reply);
                }
            }
    
            transition!{
                // consume ghost tokens and generate token for outut
                ghost_transition(lbl) {
                    require lbl is Internal;
                    require app_request <= pre.pending_app_request;
                    require io_replies <= pre.io_replies;
    
                    // app_request determines the transition
                    require s.next(new_s, lbl->app_request, lbl->io_replies, lbl->io_requests, lbl->app_replies);
    
                    update pending_app_request = pre.pending_app_request.remove(app_request);
                    update io_replies = pre.io_replies.remove(io_replies);
                    update pending_app_replies += lbl->app_replies;
                    update io_requests += lbl->io_requests;
                    update s = new_s;
                }
            }
    
            transition!{
                // consumes a token to reply
                send_app_output(lbl) {
                    require lbl is ReplyApp;
                    update pending_app_reply = pending_app_reply.remove(lbl->new_reply);
                }
            }
    
            
            // theorem: every execution of the async reply/request is equivalent to an execution 
            // where every step is atomic 
    
        }

        }
}