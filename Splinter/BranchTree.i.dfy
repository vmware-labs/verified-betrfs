include "../lib/Base/total_order.i.dfy"
include "IndirectionTable.i.dfy"
include "AllocationTable.i.dfy"
include "AllocationTableMachine.i.dfy"
include "MsgSeq.i.dfy"
//include "SplinterTree.i.dfy"
include "Message.s.dfy"
include "Interp.s.dfy"
include "CacheIfc.i.dfy"
include "../lib/DataStructures/BtreeModel.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "DiskTypes.s.dfy"

/*

  In our splinter datastructure there's two possible things that could be btrees
  The current branch in the membuffer (fully in memory -- but we can asynchronously persist the working
  branch to disk) and the branch trees in the splinter tree on disk


  Incorporation : Process of updating the splinter tree pointers such that the current branch
  (is persisted on disk) and added to the splinter tree root

  WE CAN TREAT AS THOUGH EVERYTHING IS IN THE CACHE

  Let's ignore the in memory btree in the memBuffer for now
*/
abstract module BranchTreeMod {
  import opened CacheIfc
  import BtreeModel
  import opened Maps
  import opened DiskTypesMod
  import opened Sequences

  datatype Range = Range(start: Key, end: Key)
  {
    predicate Contains(k : Key)
    {
       && lte(start, k)
       && lt(k, end)
    }
  }

  datatype Ranges = Ranges(rangeSeq : seq<Range>)
  {
    predicate Contains(k : Key)
    {
      exists i :: 0 <= i < |rangeSeq| && rangeSeq[i].Contains(k)
    }
  }

  datatype Slice = Slice(root: CU, ranges: Ranges)
  {

    function Keys() : set<Key>
    {
        set k | k in root.Keys() && ranges.Contains(k)
    }

    function I() :  map<Key, Value>
    {
      // TODO: Interpretation also needs the cache
      map k | k in Keys() :: Interpretation(root)[k]
    }
  }

  datatype Stack = Stack(slices : seq<Slice>)
  {
    function I() :  map<Key, Value>
    {
        if |slices| == 1
        then
          slices[0].I()
        else
           MapUnionPreferB(Stack(DropLast(slices)).I(), Last(slices).I())
    }
  }

  // TODO: Change --
  datatype BTreePath = BranchPath(k: Key, steps: seq<BranchStep>)
  {
    predicate ValidPrefix(cache: CacheIfc.Variables) {
      true // some path from the root
    }

    predicate Valid(cache: CacheIfc.Variables) {
      && ValidPrefix(cache)
      && true // no nodes below this one for k.
    }

    function Decode() : Value
    {
      // filter Messages on k, I guess
      var unflattenedMsgs := seq(|steps|, i requires 0<=i<|steps| => steps[i].msgs);
      var flattenedMsgs := FoldLeft(MessageFolder, map[], unflattenedMsgs);
      if k in flattenedMsgs then EvaluateMessage(flattenedMsgs[k]) else DefaultValue()
    }
  }

  datatype Skolem = // Stuff ....

  // TODO: add cache and change the interpretation to deal with messages
  function Interpretation(root : CU) : map<Key, Value>
  {
    // TODO
    {}
  }

  /*
    Recipt where we check that the chain of nodes in that lookup from the root checks out

  */
  predicate Query(cache: CacheIfc.Variables, root: CU, k: Key, v: Value)
  {

  }

  /*
    Something like check if all the cu's for this tree are reachable on disk??
  */
  predicate IsClean(root: CU, cache: CacheIfcs.Variables)
  {

  }

  // at the we check that the tree is done
  predicate IsCompaction(stack : Stack, newroot : CU)
  {
      && stack.I() == Interpretation(newroot)
  }

  // TODO:
  predicate Internal(v: Variables, v': Variables)
  {

  }

  function Alloc() : set<CU>
  {

  }

}
