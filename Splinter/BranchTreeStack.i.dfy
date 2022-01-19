include "../lib/Base/total_order.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "IndirectionTable.i.dfy"
include "AllocationTable.i.dfy"
include "AllocationTableMachine.i.dfy"
include "MsgHistory.i.dfy"
include "BranchTree.i.dfy"
include "../Spec/Message.s.dfy"
include "../Spec/StampedMap.s.dfy"
include "BranchTreeInterp.i.dfy"
include "../lib/Base/Sequences.i.dfy"


/*
 * Module that deals with transforming and using branches into stacks of range CUs
 *
 */
module BranchTreeStackMod {
  import opened CacheIfc
  import opened Options
  import opened ValueMessage
  import KeyType
  import opened StampedMapMod
  import opened DiskTypesMod
  import opened AllocationMod
  import opened MsgHistoryMod
  import IndirectionTableMod
  import opened BranchTreeMod
  import Nat_Order
  import BranchTreeInterpMod
  import opened Maps
  import opened Sequences

  //////////////////////////////////////////////////////////////////////////////
  // Define a "Stack" of branches, so we can define what it means to extract
  // the key-message pairs from a stack and compact it into a new branch tree.
  //////////////////////////////////////////////////////////////////////////////
  datatype Range = Range(start: Key, end: Key)
  {
    predicate Contains(k : Key)
    {
       && Keys.lte(start, k)
       && Keys.lt(k, end)
    }
  }

  datatype Ranges = Ranges(rangeSeq : seq<Range>)
  {
    predicate Contains(k : Key)
    {
      exists i :: 0 <= i < |rangeSeq| && rangeSeq[i].Contains(k)
    }
  }

  datatype Slice = Slice(root: CU, ranges: Ranges, cache: CacheIfc.Variables)
  {

    function Keys() : iset<Key>
    {
        iset k | k in BranchTreeInterpMod.IM(root, cache).Keys && ranges.Contains(k)
    }

    function IM() :  imap<Key, Message>
    {
      imap k | k in Keys() :: BranchTreeInterpMod.IM(root, cache)[k]
    }
  }

  datatype Stack = StackFrame(slices : seq<Slice>)
  {
    function IM() :  imap<Key, Message>
      decreases |slices|
    {
        if |slices| == 0
        then
          imap []
        else if |slices| == 1
        then
          slices[0].IM()
        else
           var stk := StackFrame(DropLast(slices));
           IMapUnionPreferB(stk.IM(), Last(slices).IM())
    }
  }



  // at the we check that the tree is done
  predicate IsCompaction(stack : Stack, newroot : CU, cache: CacheIfc.Variables)
  {
      stack.IM() == BranchTreeInterpMod.IM(newroot, cache)
  }
}
