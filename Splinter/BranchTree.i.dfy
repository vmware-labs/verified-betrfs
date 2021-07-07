include "../Spec/Message.s.dfy"
include "../Spec/Interp.s.dfy"
include "DiskTypes.s.dfy"

include "../lib/Base/total_order.i.dfy"
include "IndirectionTable.i.dfy"
include "AllocationTable.i.dfy"
include "AllocationTableMachine.i.dfy"
include "MsgHistory.i.dfy"


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
  import opened ValueMessage
  import opened KeyType
  import opened MsgHistoryMod

  import KeysImpl = Lexicographic_Byte_Order_Impl
  import Keys = KeysImpl.Ord

  type Key = Keys.Element

  // TODO: Finish and maybe we want Routing Filters here, check with Rob and Jon for this
  datatype QuotientFilter = QuotientFilter()

  // messages that are Inserted into the branch tree are already merged upon insert, that's Why
  // kvmap has to only store one merged update message per Key
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

    function findSubBranch(key: Key) : CU
      requires WF()
      requires this.Index?
    {
      // TODO switch to Rob's pivot-looker-upper
      if Keys.lt(key, pivots[0]) //TODO Check if pivots are inclusive
        then
        assert this.Index?;
        children[0]
      else if Keys.lte(pivots[|pivots| - 1], key) // Don't know if gt exists
        then
        children[|pivots|]
      else
        assert this.Index?;
        assert Keys.lt(pivots[0], key);
        assert Keys.lt(key, pivots[|pivots| - 1]);
        var pivot :| ( && 1 < pivot < |pivots|
                       && Keys.lte(pivots[pivot - 1], key)
                       && Keys.lt(key, pivots[pivot]) ); //TODO Check if pivots are inclusive
        children[pivot]
    }
  }

  // Parses CU units to BranchNodes that we can use
  function ParseBranchNode(pg : UninterpretedDiskPage) : Option<BranchNode> // TODO: Finish

  function CUToBranceNode(cu : CU, cache: CacheIfc.Variables) : Option<BranchNode>
  {
      var diskPage := ReadValue(cache, cu);
      if diskPage == None
      then
        None
      else
        ParseBranchNode(diskPage.value)
  }

  datatype Variables = Variables(root : CU, filter : QuotientFilter)
  {
    predicate WF()
    {
      true
      // TODO:
    }

    predicate Valid(cache : CacheIfc.Variables)
    {
      true
    }

    function Root() : CU
      requires WF()
    {
      root
    }
  }

  // Essentially denotes a path in the branch tree from the root cu to a corresponding leaf
  // If there are no messages corresponding to this key,
  // then the final entity in this sequence steps will be None
  datatype BranchStep = BranchStep(cu: CU, node:BranchNode)

  datatype BranchPath = BranchPath(key: Key, steps: seq<BranchStep>)
  {
    predicate WF() {
      && 0 < |steps|
      && (forall i | 0 <= i < |steps|-1 :: steps[i].node.Index?)
      && Last(steps).node.Leaf?
    }

    predicate {:opaque} Linked() {
      && (forall i | 0 < i < |steps| :: steps[i].cu == steps[i-1].node.findSubBranch(key))
    }

    predicate Valid(cache: CacheIfc.Variables) {
      && WF()
      && Linked()
      && (forall i | 0 <= i < |steps| :: Some(steps[i].node) == CUToBranceNode(steps[i].cu, cache))
    }

    function Root() : CU
      requires WF()
    {
      steps[0].cu
    }

    function CUs() : seq<CU>
      requires WF()
    {
      seq(|steps|, i requires (0 <= i < |steps|) => steps[i].cu)
    }


    function Decode() : (msg : Option<Message>)
      requires WF()
    {
      var msgs := Last(steps).node.kvmap;
      if key in msgs
      then
        Some(msgs[key])
      else
        None
    }
  }

  datatype BranchReceipt = BranchReceipt(branchPath : BranchPath, branchTree: Variables)
  {
    predicate Valid(cache : CacheIfc.Variables)
    {
      && branchPath.Valid(cache)
      && branchTree.Valid(cache)
      && branchPath.steps[0].cu == branchTree.root
      // QUESTION : Check if we need another check to compare the children of the branchTree to the branchPath
    }

  }

  datatype Skolem =
     | QueryStep(branchPath: BranchPath)
     | PutManyStep()
     | CompactBranchStep()

  /*
    Recipt where we check that the chain of nodes in that lookup from the root checks out
  */
  predicate Query(root: CU, cache: CacheIfc.Variables, key: Key, msg: Option<Message>, sk: Skolem)
  {
    && sk.QueryStep?
    && var path := sk.branchPath;
    && path.Valid(cache)
    && path.key == key
    // TODO: Check if this is what we want to do, i.e use Option
    && (msg.Some? ==> path.Decode() == msg)
  }

  /*
    Something like check if all the cu's for this tree are reachable on disk??
  */
  predicate IsClean(root: CU, cache: CacheIfc.Variables)
  {
    forall cu | cu in  Alloc() :: CacheIfc.IsClean(cache, cu)
  }

  function Alloc() : set<CU>
  {
    {} // TODO
  }

}
