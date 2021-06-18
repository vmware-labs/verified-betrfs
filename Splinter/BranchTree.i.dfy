include "Message.s.dfy"
include "Interp.s.dfy"
include "DiskTypes.s.dfy"

include "../lib/Base/total_order.i.dfy"
include "IndirectionTable.i.dfy"
include "AllocationTable.i.dfy"
include "AllocationTableMachine.i.dfy"
include "MsgSeq.i.dfy"
//include "SplinterTree.i.dfy"

include "CacheIfc.i.dfy"
include "../lib/DataStructures/BtreeModel.i.dfy"
include "../lib/Base/Maps.i.dfy"


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
  import opened Options
  import opened Maps
  import opened DiskTypesMod
  import opened Sequences

  import opened MessageMod // TODO later change the keys value type to be generic

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

    function Keys() : set<Key>
    {
        set k | k in Interpretation(root, cache).Keys && ranges.Contains(k)
    }

    function I() :  map<Key, Value>
    {
      map k | k in Keys() :: Interpretation(root, cache)[k]
    }
  }

  datatype Stack = Stack(slices : seq<Slice>)
  {
    function I() :  map<Key, Value>
      decreases |slices|
    {
        if |slices| == 0
        then
          map []
        else if |slices| == 1
        then
          slices[0].I()
        else
           MapUnionPreferB(Stack(DropLast(slices)).I(), Last(slices).I())
    }
  }

  datatype BranchNode = Leaf(kvmap: map<Key, Value>) | Index(pivots : seq<Key>, children: seq<CU>)
  {
    predicate WF()
    {
      ( this.Index? ==> ( && |pivots| + 1 == |children|
                          && 2 <= |children| // otherwise this would just be a leaf
                          && 1 <= |pivots|
                          && forall pivot :: (1 <= pivot < |pivots| && pivots[pivot - 1] < pivots[pivot])
                        )
      )
    }

    function findSubBranch(key: Key) : Option<CU>
      requires WF()
    {
      if !this.Index?
        then
        None
      else if Keys.lt(key, pivots[0]) //TODO Check if pivots are inclusive
        then
        assert this.Index?;
        Some(children[0])
      else if Keys.lte(pivots[|pivots| - 1], key) // Don't know if gt exists
        then
        Some(children[|pivots|])
      else
        assert this.Index?;
        assert Keys.lt(pivots[0], key);
        assert Keys.lt(key, pivots[|pivots| - 1]);
        var pivot :| ( && 1 < pivot < |pivots|
                       && Keys.lte(pivots[pivot - 1], key)
                       && Keys.lt(key, pivots[pivot]) ); //TODO Check if pivots are inclusive
        Some(children[pivot])
    }
  }


   // Here Check with Jon about whther we're gonna deal with values or messages
   datatype BranchStep = BranchStep(root: CU, key: Key, value: Value)


  // // TODO: Change --
   datatype BranchPath = BranchPath(k: Key, steps: seq<BranchStep>)
   {
     predicate ValidPrefix(cache: CacheIfc.Variables) {
       true // some path from the root
     }

     predicate Valid(cache: CacheIfc.Variables) {
       && ValidPrefix(cache)
       && true // no nodes below this one for k.
     }

     // function Decode() : Value
     // {
     //   // filter Messages on k, I guess
     //   //var unflattenedMsgs := seq(|steps|, i requires 0<=i<|steps| => steps[i].msgs);
     //   //var flattenedMsgs := FoldLeft(MessageFolder, map[], unflattenedMsgs);
     //   //if k in flattenedMsgs then EvaluateMessage(flattenedMsgs[k]) else DefaultValue()
     //   Value()
     // }
   }

   function BranchSteps(root: CU, key: Key) : Option<BranchPath>
   {
     //BranchPath()
     None // TODO : Finish
   }

  datatype Skolem = Skolem()

  // TODO: add cache and change the interpretation to deal with messages
  function Interpretation(root : CU, cache: CacheIfc.Variables) : map<Key, Value>
  {
    // TODO
    map []
  }

  /*
    Recipt where we check that the chain of nodes in that lookup from the root checks out

  */
  predicate Query(root: CU, cache: CacheIfc.Variables, k: Key, v: Value)
  {
    && var path := BranchSteps(root, k) ;
    && path.Some?
    && path.value.Valid(cache)
    && path.value.k == k
    //&& trunkPath.Decode() == value // TODO: finish
  }

  /*
    Something like check if all the cu's for this tree are reachable on disk??
  */
  predicate IsClean(root: CU, cache: CacheIfc.Variables)
  {
    forall cu | cu in  Alloc() :: CacheIfc.IsClean(cache, cu)
  }

  // at the we check that the tree is done
  predicate IsCompaction(stack : Stack, newroot : CU, cache: CacheIfc.Variables)
  {
      stack.I() == Interpretation(newroot, cache)
  }

  // TODO:
  predicate Internal(v: Variables, v': Variables)
  {
    false
  }

  function Alloc() : set<CU>
  {
    {} // TODO
  }

}
