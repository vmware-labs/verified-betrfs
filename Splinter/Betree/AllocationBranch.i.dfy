// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
 
include "../../lib/Base/KeyType.s.dfy"
include "../../Spec/Message.s.dfy"
include "../../lib/Base/Sets.i.dfy"
include "../../lib/Base/total_order_impl.i.dfy"
include "../Disk/GenericDisk.i.dfy"
include "FlattenedBranch.i.dfy"
//  module that introduces summary node

module AllocationBranchMod {
  import opened Maps
  import opened Options
  import opened KeyType
  import opened ValueMessage
  import opened Sequences
  import opened GenericDisk
  import opened Sets
  import opened FlattenedBranchMod
  import KeysImpl = Lexicographic_Byte_Order_Impl
  import Keys = KeysImpl.Ord

  type Address = GenericDisk.Address

  datatype TransitionLabel = 
    | QueryLabel(key: Key, msg: Message)
    | BuildLabel(ptr: Pointer, input: FlattenedBranch)

  // Design Option
  // 1. top of tree is index node, index node points to a summary node
  //    + don't need to change betree node pointers
  //    + easy to refine (just ignore the summary node field)
  //    - maintains inv that all index node has None summary node except for root
  //    - atomic recovery must have twice as many Branch pages resident
  // 2. top of tree is summary node, summar points to index
  //    - betree node's fields now point to an indirection node instead of the actual root (refinement hassle)
  //    - Summary pages need to be present in cache during steady state [primary reason for not doing 2]

  // summary describes all AUs storing this b+tree
  datatype Node = 
    | Index(pivots: seq<Key>, children: seq<Address>, summary: Pointer)
    | Leaf(keys: seq<Key>, msgs: seq<Message>)
    | Summary(aus: set<AU>)
  {
    predicate WF() {
      match this {
        case Index(pivots, children, summary) =>
          && |pivots| == |children| - 1
          && Keys.IsStrictlySorted(pivots)
        case Leaf(keys, msgs) => 
          && |keys| == |msgs|
          && Keys.IsStrictlySorted(keys)
        case Summary(_) => true
      } 
    }

    predicate ValidChildIndex(i: nat) {
      && Index?
      && i < |children|
    }

    function Route(key: Key) : int
      requires WF()
      requires !Summary?
    {
      var s := if Leaf? then keys else pivots;
      Keys.LargestLte(s, key)
    }

    // predicate CanI()
    // {
    //   && !Summary?
    // }

    // function I() : L.Node
    //   requires  CanI()
    // {
    //   if Index? then L.Index(pivots, children) else L.Leaf(keys, msgs)
    // }
  }

  datatype DiskView = DiskView(entries: map<Address, Node>) 
  {
    predicate WF() {
      && EntriesWF()
      && NoDanglingAddress()
      && NoSummaryChild()
    }

    predicate EntriesWF() {
      && (forall addr | addr in entries :: entries[addr].WF())
    }

    predicate ValidAddress(addr: Address) {
      addr in entries
    }

    predicate NodeHasValidChildAddress(node: Node) {
      node.Index? ==>
        (forall idx:nat | idx < |node.children| :: ValidAddress(node.children[idx]))
    }

    predicate NoDanglingAddress()  // i.e. disk is closed wrt to all the address in the nodes on disk
    {
      (forall addr | addr in entries :: NodeHasValidChildAddress(entries[addr]))
    }

    predicate NodeHasValidChildType(node: Node) {
      node.Index? ==>
        (forall idx:nat | idx < |node.children| && ValidAddress(node.children[idx])
          :: !entries[node.children[idx]].Summary?
        )
    }

    predicate NoSummaryChild()  // i.e. disk is closed wrt to all the address in the nodes on disk
    {
      (forall addr | addr in entries :: NodeHasValidChildType(entries[addr]))
    }

    function Get(addr: Address) : Node
      requires ValidAddress(addr)
    {
      entries[addr]
    }

    function GetKeys(addr: Address) : set<Key>
      requires ValidAddress(addr)
      requires !Get(addr).Summary?
    {
      var node := Get(addr);
      if node.Index? 
      then ( set k | k in node.pivots ) 
      else ( set k | k in node.keys )
    }

    function Representation() : set<Address>
    {
      entries.Keys
    }
  
    predicate AgreesWithDisk(other: DiskView) {
      MapsAgree(entries, other.entries)
    }

    predicate IsSubsetOf(other: DiskView) {
      && entries.Keys <= other.entries.Keys 
      && AgreesWithDisk(other)
    }

    // The node at this address has child pointers that respect ranking
    predicate NodeChildrenRespectsRank(ranking: Ranking, addr: Address)
      requires WF()
      requires addr in entries
      requires addr in ranking
    {
      && var node := entries[addr];
      && (forall childIdx:nat | node.ValidChildIndex(childIdx) ::
          && node.children[childIdx] in ranking  // ranking is closed
          && ranking[node.children[childIdx]] < ranking[addr]  // decreases
        )
    }

    // Together with NodeChildrenRespectsRank, this says that ranking is closed
    predicate ValidRanking(ranking: Ranking) 
      requires WF()
    {
      forall addr | 
        && addr in ranking 
        && addr in entries 
      ::
        && NodeChildrenRespectsRank(ranking, addr)
    }

    predicate IsFresh(addrs: set<Address>) {
      addrs !! entries.Keys
    } 

    function {:opaque} MergeDisk(other: DiskView) : (out: DiskView)
      // ensure result is sound -- keys and their values must come from one of these places
      ensures forall addr | addr in out.entries 
        :: || (addr in entries && out.entries[addr] == entries[addr])
           || (addr in other.entries && out.entries[addr] == other.entries[addr])
      // ensure result is complete -- result must contain all the keys
      ensures entries.Keys <= out.entries.Keys
      ensures other.entries.Keys <= out.entries.Keys
    {
      DiskView.DiskView(MapUnion(entries, other.entries))
    }

    function {:opaque} RemoveDisk(other: DiskView) : (out: DiskView)
      ensures forall addr :: out.ValidAddress(addr) <==> (ValidAddress(addr) && !other.ValidAddress(addr))
      ensures out.IsSubsetOf(this)
    {
      DiskView.DiskView(MapRemove(entries, other.entries.Keys))
    } 

    // returns a new diskview with the new entry inserted
    function ModifyDisk(addr: Address, item: Node) : DiskView
    {
      DiskView.DiskView(entries[addr := item])
    }

    predicate SameExcept(other: DiskView, except: set<Address>)
    {
      MapRestrict(entries, entries.Keys - except) 
        == MapRestrict(other.entries, other.entries.Keys - except)
    }

    // function I() : L.DiskView
    // {
    //   L.DiskView(map addr | addr in entries && entries[addr].CanI() :: entries[addr].I())
    // }
  }

  function EmptyDisk() : DiskView {
    DiskView.DiskView(map[])
  }
 
  datatype AllocationBranch = AllocationBranch(root: Address, diskView: DiskView)
  {
    predicate WF()
    {
      && diskView.WF()
      && HasRoot()
      && !Root().Summary?
    }

    predicate NotSealed()
      requires HasRoot()
    {
      && (Root().Index? ==> Root().summary == None)
    }

    // function I() : (out: L.AllocationBranch)
    //   requires WF()
    //   ensures out.WF()
    // {
    //   // TODO: revisit for pre post conditions
    //   L.AllocationBranch(root, diskView.I())
    // }

    predicate HasRoot() {
      && diskView.ValidAddress(root)
    }

    // predicate ValidSummary()
    //   requires HasRoot()
    // {
    //   && (Root().Index? && Root().summary.Some?
    //     ==> diskView.ValidAddress(Root().summary.value)) 
    // }

    function Root() : Node
      requires HasRoot()
    {
      diskView.Get(root)
    }

    function GetRank(ranking: Ranking) : nat
      requires WF()
    {
      if root in ranking then ranking[root]+1 else 0
    }

     predicate ValidRanking(ranking: Ranking) 
      requires WF()
    {
      && diskView.ValidRanking(ranking)
      && root in ranking  // ranking covers tree from this root
    }

    function TheRanking() : Ranking
      requires Acyclic()
    {
      var out :| ValidRanking(out);
      out
    }

    predicate Acyclic()
    {
      && WF()
      && (exists ranking :: ValidRanking(ranking))
    }

    predicate AllKeysInRange()
      requires Acyclic()
    {
      && AllKeysInRangeInternal(TheRanking())
    }

    predicate AllKeysInRangeInternal(ranking: Ranking)
      requires WF()
      requires ValidRanking(ranking)
      decreases GetRank(ranking), 1
    {
      && (Root().Index? ==> 
        && (forall i :: 0 <= i < |Root().children| ==> ChildAtIdx(i).AllKeysInRangeInternal(ranking))
        && (forall i :: 0 <= i < |Root().children|-1 ==> AllKeysBelowBound(i, ranking))
        && (forall i :: 0 < i < |Root().children| ==> AllKeysAboveBound(i, ranking))
      )
    }

    function AllKeys(ranking: Ranking) : (result: set<Key>)
      requires WF()
      requires ValidRanking(ranking)
      decreases GetRank(ranking), 1
    {
      var node := Root();
      if node.Leaf? then (
        var result := set k | k in node.keys;
        assert 0 < |node.keys| ==> node.keys[0] in result;
        result
      ) else if node.Index? then (
        var pivotKeys := (set k | k in node.pivots);
        var indexKeys := (set i, k | 0 <= i < |node.children| && k in ChildAtIdx(i).AllKeys(ranking) :: k);
      
        var result := pivotKeys + indexKeys;
        assert 0 < |node.pivots| ==> node.pivots[0] in result;
        result
      ) else ( 
        {}
      )
    }

    predicate AllKeysBelowBound(i: int, ranking: Ranking)
      requires WF()
      requires ValidRanking(ranking)
      requires Root().Index?
      requires 0 <= i < |Root().pivots|
      decreases GetRank(ranking)
    {
      forall key :: key in ChildAtIdx(i).AllKeys(ranking) ==> Keys.lt(key, Root().pivots[i])
    }

     predicate AllKeysAboveBound(i: int, ranking: Ranking)
      requires WF()
      requires ValidRanking(ranking)
      requires Root().Index?
      requires 0 <= i-1 < |Root().pivots|
      decreases GetRank(ranking)
    {
      forall key :: key in ChildAtIdx(i).AllKeys(ranking) ==> Keys.lte(Root().pivots[i-1], key)
    }

    function ChildAtIdx(idx: nat) : (result: AllocationBranch)
      requires HasRoot()
      requires Root().ValidChildIndex(idx)
      ensures WF() ==> result.WF()
      ensures Acyclic() ==> result.Acyclic()
    {
      var result := AllocationBranch(Root().children[idx], diskView);
      assert Acyclic() ==> result.Acyclic() by {
        if Acyclic() {
          assert result.ValidRanking(TheRanking()); 
        }
      }
      result
    }

    function Representation() : set<Address>
      requires Acyclic()
    {
      var summary := if Root().Index? && Root().summary.Some? 
        then { Root().summary.value } else {};
      var treeRepr := ReachableAddrsUsingRanking(TheRanking());
      treeRepr + summary
    }

    function ReachableAddrsUsingRanking(ranking: Ranking) : (out: set<Address>)
      requires WF()
      requires ValidRanking(ranking)
      ensures HasRoot() ==> root in out
      ensures out <= diskView.entries.Keys
      decreases GetRank(ranking)
    {
      if !HasRoot() then {}
      else if Root().Summary? then {root} // not reachable, root will never be a summary type node by Inv
      else if Root().Leaf? then {root}
      else
        var numChildren := |Root().children|;
        var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));

        UnionSeqOfSetsSoundness(subTreeAddrs);
        {root} + UnionSeqOfSets(subTreeAddrs)
    }

    function RepresentationAUs() : set<AU>
      requires Acyclic()
    {
      set addr | addr in  Representation() :: addr.au
    }

    predicate TightDiskView()
    {
      && (Acyclic() ==> (Representation() == diskView.Representation()))
    }

    function QueryInternal(key: Key, ranking: Ranking) : (msg: Message)
      requires WF()
      requires ValidRanking(ranking)
      decreases GetRank(ranking)
    {
      var node := Root();
      var r := node.Route(key);
      if node.Leaf? then (
        if r >= 0 && node.keys[r] == key
        then node.msgs[r] else Update(NopDelta())
      ) else (
        ChildAtIdx(r+1).QueryInternal(key, ranking)
      )
    }

    function Query(key: Key) : (msg: Message)
    {
      if Acyclic()
      then QueryInternal(key, TheRanking())
      else Update(NopDelta()) // Dummy value    
    }

    // mutable operation

    // Grow
    function Grow(addr: Address) : (out: AllocationBranch)
    {
      var newRoot := Index([], [root], None);
      var newDiskView := diskView.ModifyDisk(addr, newRoot);
      AllocationBranch(addr, newDiskView)
    }

    // Insert
    function InsertLeaf(key: Key, msg: Message) : (result: AllocationBranch)
    requires WF()
    requires Root().Leaf?
    ensures result.WF()
    {
      var node := Root();
      var llte := Keys.LargestLte(node.keys, key);
      var newNode :=
        if 0 <= llte && node.keys[llte] == key  then 
          Leaf(node.keys, node.msgs[llte := msg])
        else 
          assert Keys.IsStrictlySorted(insert(node.keys, key, llte+1)) by {
            reveal_insert();
            Keys.reveal_IsStrictlySorted();
          }
          Leaf(insert(node.keys, key, llte+1), insert(node.msgs, msg, llte+1));

      AllocationBranch(root, diskView.ModifyDisk(root, newNode))
    }

    // Append
    function AppendToNewLeaf(newKeys: seq<Key>, newMsgs: seq<Message>) : (result: AllocationBranch)
    requires WF()
    requires Root().Leaf?
    requires |newKeys| == |newMsgs|
    requires Keys.IsStrictlySorted(newKeys)
    ensures result.WF()
    {
      var newNode := Leaf(newKeys, newMsgs);
      var newDiskView := diskView.ModifyDisk(root, newNode);
      AllocationBranch(root, newDiskView)
    }

    // Split

    predicate SplitLeaf(pivot: Key, leftLeaf: AllocationBranch, rightLeaf: AllocationBranch)
    {
      && HasRoot()
      && Root().Leaf?
      && leftLeaf.HasRoot()
      && leftLeaf.Root().Leaf?
      && rightLeaf.HasRoot()
      && rightLeaf.Root().Leaf?

      && leftLeaf.root == root
      && rightLeaf.diskView == leftLeaf.diskView

      && 0 < |leftLeaf.Root().keys| == |leftLeaf.Root().msgs|
      && 0 < |rightLeaf.Root().keys| == |rightLeaf.Root().msgs|

      && Root().keys == leftLeaf.Root().keys + rightLeaf.Root().keys
      && Root().msgs == leftLeaf.Root().msgs + rightLeaf.Root().msgs
      && Keys.lt(Last(leftLeaf.Root().keys), pivot)
      && Keys.lte(pivot, rightLeaf.Root().keys[0])
    }

    function SubIndex(from: int, to: int) : (result : Node)
    requires HasRoot()
    requires Root().Index?
    requires |Root().children| == |Root().pivots| + 1
    requires 0 <= from < to <= |Root().children|
    {
      Index(Root().pivots[from..to-1], Root().children[from..to], None)
    }

    predicate SplitIndex(pivot: Key, leftIndex: AllocationBranch, rightIndex: AllocationBranch)
    {
      && HasRoot()
      && Root().Index?
      && leftIndex.HasRoot()
      && leftIndex.Root().Index?
      && rightIndex.HasRoot()
      && rightIndex.Root().Index?

      && leftIndex.root == root
      && rightIndex.diskView == leftIndex.diskView

      && 0 < |leftIndex.Root().children| < |Root().children|
      && |Root().children| == |Root().pivots| + 1
      && leftIndex.Root() == SubIndex(0, |leftIndex.Root().children|)
      && rightIndex.Root() == SubIndex(|leftIndex.Root().children|, |Root().children|)
      && (leftIndex.Acyclic() && rightIndex.Acyclic()  ==>
        && var leftLastChild := leftIndex.ChildAtIdx(|leftIndex.Root().children|-1);
        && var rightFirstChild := rightIndex.ChildAtIdx(0);
        && (forall key :: key in leftLastChild.AllKeys(leftLastChild.TheRanking()) ==> Keys.lt(key, pivot))
        && (forall key :: key in rightFirstChild.AllKeys(rightFirstChild.TheRanking()) ==> Keys.lte(pivot, key))
      )
      && pivot == Root().pivots[|leftIndex.Root().pivots|]
    }

    predicate SplitNode(pivot: Key, leftBranch: AllocationBranch, rightBranch: AllocationBranch)
    {
      || SplitLeaf(pivot, leftBranch, rightBranch)
      || SplitIndex(pivot, leftBranch, rightBranch)
    }

    predicate SplitChildOfIndex(pivot: Key, newChildAddr: Address, newIndex: AllocationBranch)
    {
      && HasRoot()
      && Root().Index?
      && Root().WF() // I mean... we can do something more relaxed here but WF should be easy to prove right?
      && newIndex.HasRoot()
      && newIndex.Root().Index?
      && newIndex.root == root

      && var childIdx := Root().Route(pivot)+1;
      && newIndex.Root().pivots == insert(Root().pivots, pivot, childIdx)
      && newIndex.Root().children == insert(Root().children, newChildAddr, childIdx+1)
      && ChildAtIdx(childIdx).SplitNode(pivot, newIndex.ChildAtIdx(childIdx), newIndex.ChildAtIdx(childIdx+1))
      && diskView.SameExcept(newIndex.diskView,
        {newIndex.root, newIndex.ChildAtIdx(childIdx).root, newIndex.ChildAtIdx(childIdx+1).root})
    }
  }

  function EmptyAllocationBranch(root: Address) : (result: AllocationBranch)
    ensures result.WF()
  {
    AllocationBranch(root, EmptyDisk().ModifyDisk(root, Leaf([], [])))
  }

  datatype Path = Path(branch: AllocationBranch, key: Key, depth: nat)
  {
    function Subpath() : (out: Path)
      requires 0 < depth
      requires branch.WF()
      requires branch.Root().Index?
    {
      var r := branch.Root().Route(key)+1;
      Path(branch.ChildAtIdx(r), key, depth-1)
    }

    predicate Valid()
      decreases depth
    {
      && branch.WF()
      && (0 < depth ==> branch.Root().Index?)
      && (0 < depth ==> Subpath().Valid())
    }

    function Target() : (out: AllocationBranch)
      requires Valid()
      ensures out.WF()
      decreases depth
    {
      if 0 == depth
      then branch
      else Subpath().Target()
    }

    function Substitute(replacement: AllocationBranch) : (out: AllocationBranch)
      requires Valid()
    {
      AllocationBranch(branch.root, replacement.diskView)
    }

    predicate PathEquiv(otherKey: Key)
      requires Valid()
      decreases depth, 1
    {
      && branch.Root().Route(key) == branch.Root().Route(otherKey)
      && (0 < depth ==> Subpath().PathEquiv(otherKey))
    }
  }

  datatype Variables = Variables(branch: AllocationBranch)
  {
    predicate WF() {
      branch.WF()
    }
  }

  predicate Query(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.QueryLabel?
    && v.WF()
    && v.branch.Query(lbl.key) == lbl.msg
    && v' == v
  }

  predicate Insert(v: Variables, v': Variables, lbl: TransitionLabel, path: Path, newTarget: AllocationBranch)
  {
    && lbl.BuildLabel?
    && lbl.ptr.None?
    && lbl.input.WF()
    && |lbl.input.keys| == 1
    && v.WF()
    && v.branch.NotSealed()
    && path.Valid()
    && path.branch == v.branch
    && path.key == lbl.input.keys[0]
    && path.Target().Root().Leaf?
    && newTarget == path.Target().InsertLeaf(lbl.input.keys[0], lbl.input.msgs[0])
    && v'.branch == path.Substitute(newTarget)
  }

  predicate Append(v: Variables, v': Variables, lbl: TransitionLabel, path: Path, newTarget: AllocationBranch)
  {
    && lbl.BuildLabel?
    && lbl.ptr.None?
    && lbl.input.WF()
    && lbl.input.keys != []
    && v.WF()
    && v.branch.NotSealed()
    && path.Valid()
    && path.branch == v.branch
    && path.Target().Root() == Leaf([], [])
    && newTarget == path.Target().AppendToNewLeaf(lbl.input.keys, lbl.input.msgs)
    && path.key == lbl.input.keys[0]
    && path.PathEquiv(Last(lbl.input.keys))
    && v'.branch == path.Substitute(newTarget)
  }

  predicate Grow(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.BuildLabel?
    && lbl.input.IsEmpty()
    && lbl.ptr.Some?
    && v.WF()
    && v.branch.NotSealed()
    && v.branch.diskView.IsFresh({lbl.ptr.value})
    && v'.branch == v.branch.Grow(lbl.ptr.value)
  }

  predicate Split(v: Variables, v': Variables, lbl: TransitionLabel, 
    path: Path, pivot: Key, newTarget: AllocationBranch)
  {
    && lbl.BuildLabel?
    && lbl.input.IsEmpty()
    && lbl.ptr.Some?
    && v.WF()
    && v.branch.NotSealed()
    && path.Valid()
    && v.branch.diskView.IsFresh({lbl.ptr.value})
    && path.branch.root == v.branch.root
    && path.Target().SplitChildOfIndex(pivot, lbl.ptr.value, newTarget)
    && v'.branch == path.Substitute(newTarget)
  }

  predicate Seal(v: Variables, v': Variables, lbl: TransitionLabel, node: Node)
  {
    && lbl.BuildLabel?
    && lbl.input.IsEmpty()
    && lbl.ptr.Some?
    && v.WF()
    && v.branch.NotSealed()
    && v.branch.Root().Index?
    && v.branch.diskView.IsFresh({lbl.ptr.value})
    && node.Summary?
    // Jon: it's possible to not have the summary node store its au
    && node.aus == (
      if v.branch.Acyclic()
      then v.branch.RepresentationAUs() + { lbl.ptr.value.au }
      else { lbl.ptr.value.au } // dummy case
    )
    && var newRoot := v.branch.Root().(summary := Some(lbl.ptr.value));
    && v'.branch.root == v.branch.root
    && v'.branch.diskView == v.branch.diskView.ModifyDisk(lbl.ptr.value, node).ModifyDisk(v.branch.root, newRoot)
  }

  // public:

  predicate Init(v: Variables)
  {
    && v.branch == EmptyAllocationBranch(v.branch.root)
  }

  datatype Step =
    | QueryStep()
    | InsertStep(path: Path, newTarget: AllocationBranch)
    | AppendStep(path: Path, newTarget: AllocationBranch)
    | GrowStep()
    | SplitStep(path: Path, pivot: Key, newTarget: AllocationBranch)
    | SealStep(node: Node)

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case QueryStep() => Query(v, v', lbl)
      case InsertStep(path, newTarget) => Insert(v, v', lbl, path, newTarget)
      case AppendStep(path, newTarget) => Append(v, v', lbl, path, newTarget)
      case GrowStep() => Grow(v, v', lbl)
      case SplitStep(path, pivot, newTarget) => Split(v, v', lbl, path, pivot, newTarget)
      case SealStep(node) => Seal(v, v', lbl, node)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }
}


