include "../../lib/Lang/NativeTypes.s.dfy"
include "../framework/PCM.s.dfy"
include "../framework/Ptrs.s.dfy"
include "../framework/Atomic.s.dfy"
include "../framework/MultiRw.i.dfy"
include "QueueMultiRw.i.dfy"

abstract module QueueImpl {
  import opened GhostLoc
  import opened Ptrs
  import opened NativeTypes
  import opened Atomics
  import Tokens = MultiRwTokens(QueueMultiRw)

  type Item(!new)

  linear datatype ConsumerToken = ConsumerToken(glinear token: Token, tail: uint32)

  datatype Queue = Queue(
    cells: seq<Ptr>,
    head: Atomic<uint32, Token>,
    tail: Atomic<uint32, Token>,

    ghost cellToken: GhostAtomic<Token>,
    ghost loc: Loc
  ) {

    method consume(linear consumerToken: ConsumerToken) returns (
      linear consumerToken': ConsumerToken, linear item: Item)
    {
      atomic_block var ret_value := execute_atomic_load(this.head) {
        ghost_acquire head_g;
        atomic_block var _ := execute_atomic_noop(this.cellToken) {
          ghost_acquire cellToken_g;

          ghost_release cellToken_g;
        }
        ghost_release head_g;
      }
    }

  }
  
}
