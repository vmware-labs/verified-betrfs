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
include "../lib/Buckets/BoundedPivotsLib.i.dfy"


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
  import opened BoundedPivotsLib



  // TODO: Finish and maybe we want Routing Filters here, check with Rob and Jon for this
  datatype QuotientFilter = QuotientFilter()

  // messages that are Inserted into the branch tree are already merged upon insert, that's Why
  // kvmap has to only store one merged update message per Key
  datatype BranchNode = | Leaf(kvmap: map<Key, Message>)
                        | Index(pivots : PivotTable, children: seq<CU>)
  {

    predicate WFIndexNode()
      requires this.Index?
    {
      && WFPivots(pivots)
      && |children| == NumBuckets(pivots)
    }

    predicate WF()
    {
      this.Index? ==> WFIndexNode()
    }

    // function findSubBranch(key: Key) : CU
    //   requires WF()
    //   requires this.Index?
    // {
    //   assume false; // TODO kill this function; replace with pivot lib
    //   // TODO switch to Rob's pivot-looker-upper
    //   if Keys.lt(key, pivots[0]) //TODO Check if pivots are inclusive
    //     then
    //     assert this.Index?;
    //     children[0]
    //   else if Keys.lte(pivots[|pivots| - 1], key) // Don't know if gt exists
    //     then
    //     children[|pivots|]
    //   else
    //     assert this.Index?;
    //     assert Keys.lt(pivots[0], key);
    //     assert Keys.lt(key, pivots[|pivots| - 1]);
    //     var pivot :| ( && 1 < pivot < |pivots|
    //                    && Keys.lte(pivots[pivot - 1], key)
    //                    && Keys.lt(key, pivots[pivot]) ); //TODO Check if pivots are inclusive
    //     children[pivot]
    // }
  }

  // Parses CU units to BranchNodes that we can use
  function ParseBranchNode(pg : UninterpretedDiskPage) : Option<BranchNode> // TODO: Finish

  function CUToBranchNode(cu : CU, cache: CacheIfc.Variables) : Option<BranchNode>
  {
      var diskPage := ReadValue(cache, cu);
      if diskPage == None
      then
        None
      else
        ParseBranchNode(diskPage.value)
  }

  // TODO change name of variables BranchTree
  datatype Variables = Variables(root : CU, filter : QuotientFilter)
  {
    predicate WF()
    {
      true
      // TODO:
    }

    predicate Valid(cache : CacheIfc.Variables)
    {
      && root in CUsInDisk()
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
  {
    predicate WF() {
      && node.WF()
    }
  }

  datatype BranchPath = BranchPath(key: Key, steps: seq<BranchStep>)
  {
    predicate WF() {
      && 0 < |steps|
      && (forall i | 0 <= i < |steps| :: steps[i].WF())
      && (forall i | 0 <= i < |steps|-1 :: steps[i].node.Index?)
      && Last(steps).node.Leaf?
      // BoundedKey is derivable from ContainsRange, but that requires a mutual induction going down
      // the tree. It's easier to demand forall-i-BoundedKey so that we can call Route to get the slots
      // for ContainsRange.
      && (forall i | 0 <= i < |steps|-1 :: BoundedKey(steps[i].node.pivots, key))
    }

    predicate LinkedAt(childIdx : nat)
      requires 0 < childIdx < |steps|-1
      requires WF()
    {
      && var parentNode := steps[childIdx-1].node;
      && var childStep := steps[childIdx];
      && var slot := Route(parentNode.pivots, key);
      // When coverting to clone edges use, ParentKeysInChildRange in TranslationLib
      && ContainsRange(childStep.node.pivots, parentNode.pivots[slot], parentNode.pivots[slot+1])
      && childStep.cu == parentNode.children[slot]
    }

    predicate {:opaque} Linked()
      requires WF()
    {
      && (forall i | 0 < i < |steps|-1 :: LinkedAt(i))
    }

    predicate Valid(cache: CacheIfc.Variables) {
      && WF()
      && Linked()
      && (forall i | 0 <= i < |steps| :: Some(steps[i].node) == CUToBranchNode(steps[i].cu, cache))
    }

    function Root() : (cu :CU)
      requires WF()
      ensures cu == steps[0].cu
    {
      steps[0].cu
    }

    // function CUs() : seq<CU>
    //   requires WF()
    // {
    //   seq(|steps|, i requires (0 <= i < |steps|) => steps[i].cu)
    // }

    // TODO: Refactor CUS ensures into another ValidCUs predicate

    // Return the sequence of CUs (aka nodes) this path touches
    function {:opaque} CUsRecurse(count : nat) : (cus : seq<CU>)
      requires WF()
      requires count <= |steps|
      ensures (forall i | 0<=i<count :: steps[i].cu in cus)
    {
       if count == 0
       then
         []
       else
         [steps[count-1].cu] + CUsRecurse(count-1)
    }

    // Return the sequence of CUs (aka nodes) this path touches
    function {:opaque} CUs() : (cus: seq<CU>)
      requires WF()
      ensures (forall i | 0<=i<|steps| :: steps[i].cu in cus)
    {
      CUsRecurse(|steps|)
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
    predicate WF() {
      && branchPath.WF()
      && branchTree.WF()
      && 0 < |branchPath.steps|
      && (branchTree.Root() == branchPath.steps[0].cu)
    }

    predicate ValidCUs()
    {
      && var cus := branchPath.CUs();
      && (forall i | 0<=i<|branchPath.steps| :: branchPath.steps[i].cu in cus)
      && (forall cu | cu in cus :: cu in CUsInDisk())

    }

    predicate Valid(cache : CacheIfc.Variables)
    {
      && WF()
      && branchPath.Valid(cache)
      && branchTree.Valid(cache)
      && branchPath.steps[0].cu == branchTree.root
      // QUESTION : Check if we need another check to compare the children of the branchTree to the branchPath
      && ValidCUs()
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
