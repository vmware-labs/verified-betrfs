include "../lib/Base/total_order.i.dfy"
include "IndirectionTable.i.dfy"
include "AllocationTable.i.dfy"
include "AllocationTableMachine.i.dfy"
include "MsgHistory.i.dfy"
include "BranchTree.i.dfy"
include "SplinterTree.i.dfy"
include "../Spec/Message.s.dfy"
include "../Spec/Interp.s.dfy"


module BranchTreeInterpMod {
  import opened Options
  import opened ValueMessage
  import KeyType
  import opened InterpMod
  import opened DiskTypesMod
  import opened AllocationMod
  import opened MsgHistoryMod
  import IndirectionTableMod
  import opened BranchTreeMod
  import SplinterTreeMachineMod
  import Nat_Order

  type Lookup = BranchPath

  //function IMLookup()

  // NOtE: These might not be needed.
  function IMKey(root: CU, cache: CacheIfc.Variables, key: Key) : Message
  {
    if exists msg, sk :: Query(root, cache, key, msg, sk) // always true by invariant
    then
      var msg, sk :| Query(root, cache, key, msg, sk);
      if msg.Some?
      then
        msg.value
      else
        DefaultMessage()
    else
      // We should never get here
      DefaultMessage()
  }

  function IM(root : CU, cache: CacheIfc.Variables) : imap<Key, Message>
  {
    imap k | true :: IMKey(root, cache, k)
  }

  function IReadsKey(v: Variables, cache: CacheIfc.Variables, key: Key) : set<CU>

}
