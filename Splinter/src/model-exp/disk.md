
Player 1:

- AsyncDisk_t.rs // specific disk I/O 
    
- main_t.rs     // connects program with disk I/O requests?
    - system enforce I/O rules on PSM interacting with disk

- Single threaded world: player one writes a main loop that requires atomic step taken at each iteration of the loop
    - Player 1 enforce correspondance and I/O in each loop iterations
    - FSCQ? 

- Mulithreaded world: 
    - Application coorespondance (UIOp like)
    - I/O observability (I/O label provided by player 1, player 2 can use the object to take a step)
    - p2main( io, psm_perm (ghost) )
        - control loop no longer in p1
        - permission still given out by p1 


Different main loop:
- option1: p1 controlled flow & printing: while true ( do p2() print(o) )
- option2: p1 controlled flow, p2 uses I/O, but must passes the assertion check by player 1  at the end of each step
    - I/O object is the only way to access methods that actually issue I/O
- option3: p1 forces p2 to follow obligations, but doesn't care about when things are done
    - ghost story about SM, physical story impl / access to I/O (response to user, not disk I/O)
    - ironsync
        - physical state overlaps, ghost updates are atomic (have linearization order)
    // internal op are reflected as no op ui?

- Refinement to top level spec enforcement

Player 2 needs:
- a program (concrete implementation)
- supply a Program State Machine model (abstracted impl)
    - program refines to the PSM
    - Player 1 supplies a system model (main_t.rs?) that takes in an arbitrary PSM that interacts with disk
    - System model with PSM refines to top level spec (AsyncMap_t (no knowledge of a disk))


IO Perm 
- what we can use to 


- [ ] AsyncDisk_t ( model of disk )

- [ ] System_t (system model) < AsyncStateMachine >
    - [ ] this should actually take a Async SM
    - [ ] PSM => a single driver interacting with the model of system

- [] Main_t (player 1 calling player 2's entry point)
    - main(<P2Trait>)


- P2Trait [ Obligation_t.rs ] must be implemented by player 2
    - [X] p2 main 
    - [X] Program Model
    - [X] System Refinemnt proof (based on the program model?)

- P2 
    - [ ] Trait for application correspondence (APPIO_Perm)
    - [ ] Trait for IO correspondence 
        - [ ] can invoke op on struct 
    - [ ] Trait for IO linearization rules
        - [ ] without linearization rules, there might be execution in the chunky state machine that have no refinement

- [ ] Program => Implementation
    - struct variables ?


2 types of concurrency 
- memory concurrency
- disk request concurrency
    - delayed write can be moved to when transition takes place
    - until write is issued and heard back it's not in the cache??
        - user_test1 user_test2
            - read                  - read cached writes (have not written back)
            - no disk write yet     - issue a related disk write (gets carried out)
                - change is present in the cache
        - it's not possible for this to happen for super block write [ disk buffer allows for request to be dropped upon a crash ]
        - crash safe related 

