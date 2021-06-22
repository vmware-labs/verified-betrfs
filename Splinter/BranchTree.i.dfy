include "Message.s.dfy"
include "Interp.s.dfy"
include "DiskTypes.s.dfy"

include "../lib/Base/total_order.i.dfy"
include "IndirectionTable.i.dfy"
include "AllocationTable.i.dfy"
include "AllocationTableMachine.i.dfy"
include "MsgSeq.i.dfy"

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

  TODOS : Garbage collection on flushes
  TODDS : Figure out how to read a node from the CU -- DONE!!
*/

// Immutable BranchTrees that are part of the SplinterTree on disk
module BranchTreeMod {
  import opened CacheIfc
  //import BtreeModel -- THIS IS AN ABSTRACT MODULE ... WE CAN'T USE IT!!!!
  import opened Options
  import opened Maps
  import opened DiskTypesMod
  import opened Sequences

  // TODO later change the keys value type to be generic
  import opened MessageMod
  import opened MsgSeqMod

  import KeysImpl = Lexicographic_Byte_Order_Impl
  import Keys = KeysImpl.Ord

  type Key = Keys.Element


  // Ranges
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
        iset k | k in Interpretation(root, cache).Keys && ranges.Contains(k)
    }

    function I() :  imap<Key, Value>
    {
      imap k | k in Keys() :: Interpretation(root, cache)[k]
    }
  }

  datatype Stack = Stack(slices : seq<Slice>)
  {
    function I() :  imap<Key, Value>
      decreases |slices|
    {
        if |slices| == 0
        then
          imap []
        else if |slices| == 1
        then
          slices[0].I()
        else
           IMapUnionPreferB(Stack(DropLast(slices)).I(), Last(slices).I())
    }
  }

  datatype BranchNode = Leaf(kvmap: map<Key, Message>) | Index(pivots : seq<Key>, children: seq<CU>)
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

  // TODO: Finish
  // Parses CU units to BranchNodes that we can use
  function parse(pg : UninterpretedDiskPage) : Option<BranchNode>

  function CUToNode(node : CU, cache: CacheIfc.Variables) : Option<BranchNode>
  {
      var diskPage := ReadValue(cache, node);
      if diskPage == None
      then
        None
      else
        parse(diskPage.value)
  }

   // Essentially denotes a path in the branch tree from the root cu to a corresponding leaf
   // If there are no messages corresponding to this key,
   // then the final entity in this sequence steps will be None
   datatype BranchPath = BranchPath(k: Key, root: CU, cache: CacheIfc.Variables)
   {
     predicate ValidPrefix() {
       true // some path from the root
     }

     predicate Valid() {
       && ValidPrefix()
     }

     function Decode() : MsgSeq
     {
       Empty()
       //var subBranch := findSubBranch();
     }

   }

  function BranchSteps(key: Key, root: CU, cache: CacheIfc.Variables) : Option<BranchPath>
  {
   //   if CUToNode(root, cache).None?
   //   then
   //    [] // TODO : Finish
   //   else if CUToNode(root, cache).value.Leaf?
   //   then
   //    [BranchStep(root, key, root.value.)]
   //   else
   //   then
   //    var childSteps := root.value.findSubBranch(key)
   //    [root.value] + BranchSteps(key, childNode, cache)
   None // TODO
   }

   // QUESTION: DO WE EVEN NEED THIS AT THIS LAYER. ALL THE ACTUAL INTERAL STEPS
   // ARE CALLED AT IN SPLINTERINTERAL STEP????
   datatype Skolem =
     | QueryStep(branchPath: BranchPath)
     | PutManyStep()
     | CompactBranchStep()

  // TODO: add cache and change the interpretation to deal with messages
  // QUESTION : Check if its the right type imap<Key, Message> or imap<Key, MsgSeq> ????
  function Interpretation(root : CU, cache: CacheIfc.Variables) : imap<Key, Value>
  {
    // TODO
    imap []
  }

  /*
    Recipt where we check that the chain of nodes in that lookup from the root checks out
    TODO: Check if these msgs should be map<Key, Message> or map<Key, MsgSeq> . Splintertree seems to expect map<Key, Message>?
  */
  predicate Query(root: CU, cache: CacheIfc.Variables, k: Key, msgs: MsgSeq)
  {
    && var path := BranchSteps(k, root, cache) ;
    && path.Some?
    && path.value.Valid()
    && path.value.k == k
    && path.value.Decode() == msgs
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
  predicate BranchInternal(v: Variables, v': Variables)
  {
    false
  }

  function Alloc() : set<CU>
  {
    {} // TODO
  }

}
