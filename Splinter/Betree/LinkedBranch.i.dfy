// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
 
include "../../lib/Base/KeyType.s.dfy"
include "../../Spec/Message.s.dfy"
include "../../lib/Base/Option.s.dfy"
include "../../lib/Base/Maps.i.dfy"
include "../../lib/Base/Sets.i.dfy"
include "../../lib/Base/Sequences.i.dfy"
include "../../lib/Base/total_order_impl.i.dfy"
include "../Disk/GenericDisk.i.dfy"
include "PivotBranch.i.dfy"
include "Domain.i.dfy"

// LinkedBranch module stores each node in the b+tree on a different disk address

module LinkedBranchMod {
  import opened Maps
  import opened Options
  import opened KeyType
  import opened ValueMessage
  import opened Sequences
  import opened DomainMod
  import opened GenericDisk
  import opened Sets
  import KeysImpl = Lexicographic_Byte_Order_Impl
  import Keys = KeysImpl.Ord
  import P = PivotBranchMod

  type Address = GenericDisk.Address

  datatype TransitionLabel = 
    | QueryLabel(key: Key, msg: Message)
    | InsertLabel(key: Key, msg: Message)
    | AppendLabel(keys: seq<Key>, msgs: seq<Message>) // insert into a new leaf
    | InternalLabel(addr: Address)

  datatype Node = Index(pivots: seq<Key>, children: seq<Address>) | Leaf(keys: seq<Key>, msgs: seq<Message>)
  {
    predicate WF() {
      if Leaf? then 
        && |keys| == |msgs|
        && Keys.IsStrictlySorted(keys)
      else
        && |pivots| == |children| - 1
        && Keys.IsStrictlySorted(pivots)
    }

    predicate ValidChildIndex(i: nat) {
      && Index?
      && i < |children|
    }

    function Route(key: Key) : int
      requires WF()
    {
      var s := if Leaf? then keys else pivots;
      Keys.LargestLte(s, key)
    }
  }

  datatype DiskView = DiskView(entries: map<Address, Node>) 
  {
    predicate WF() {
      && EntriesWF()
      && NoDanglingAddress()
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

    function Get(addr: Address) : Node
      requires ValidAddress(addr)
    {
      entries[addr]
    }

    function GetKeys(addr: Address) : set<Key>
      requires ValidAddress(addr)
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
        NodeChildrenRespectsRank(ranking, addr)
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
  }

  function EmptyDisk() : DiskView {
    DiskView.DiskView(map[])
  }
 
  datatype LinkedBranch = LinkedBranch(root: Address, diskView: DiskView)
  {
    predicate WF()
    {
      && diskView.WF()
      && HasRoot()
    }

    predicate HasRoot() {
      && diskView.ValidAddress(root)
    }

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
      ) else (
        var pivotKeys := (set k | k in node.pivots);
        var indexKeys := (set i, k | 0 <= i < |node.children| && k in ChildAtIdx(i).AllKeys(ranking) :: k);
      
        var result := pivotKeys + indexKeys;
        assert 0 < |node.pivots| ==> node.pivots[0] in result;
        result
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

    function ChildAtIdx(idx: nat) : (result: LinkedBranch)
      requires HasRoot()
      requires Root().ValidChildIndex(idx)
      ensures WF() ==> result.WF()
      ensures Acyclic() ==> result.Acyclic()
    {
      var result := LinkedBranch(Root().children[idx], diskView);
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
      ReachableAddrsUsingRanking(TheRanking())
    }

    function ReachableAddrsUsingRanking(ranking: Ranking) : (out: set<Address>)
      requires WF()
      requires ValidRanking(ranking)
      ensures HasRoot() ==> root in out
      ensures out <= diskView.entries.Keys
      decreases GetRank(ranking)
    {
      if !HasRoot() then {}
      else if Root().Leaf? then {root}
      else
        var numChildren := |Root().children|;
        var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));

        UnionSeqOfSetsSoundness(subTreeAddrs);
        {root} + UnionSeqOfSets(subTreeAddrs)
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
    function Grow(addr: Address) : (out: LinkedBranch)
    {
      var newRoot := Index([], [root]);
      var newDiskView := diskView.ModifyDisk(addr, newRoot);
      LinkedBranch(addr, newDiskView)
    }

    // Insert
    function InsertLeaf(key: Key, msg: Message) : (result: LinkedBranch)
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

      LinkedBranch(root, diskView.ModifyDisk(root, newNode))
    }

    // Append
    function AppendToNewLeaf(newKeys: seq<Key>, newMsgs: seq<Message>) : (result: LinkedBranch)
    requires WF()
    requires Root().Leaf?
    requires |newKeys| == |newMsgs|
    requires Keys.IsStrictlySorted(newKeys)
    ensures result.WF()
    {
      var newNode := Leaf(newKeys, newMsgs);
      var newDiskView := diskView.ModifyDisk(root, newNode);
      LinkedBranch(root, newDiskView)
    }

    // Split

    predicate SplitLeaf(pivot: Key, leftLeaf: LinkedBranch, rightLeaf: LinkedBranch)
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
      Index(Root().pivots[from..to-1], Root().children[from..to])
    }

    predicate SplitIndex(pivot: Key, leftIndex: LinkedBranch, rightIndex: LinkedBranch)
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

    predicate SplitNode(pivot: Key, leftBranch: LinkedBranch, rightBranch: LinkedBranch)
    {
      || SplitLeaf(pivot, leftBranch, rightBranch)
      || SplitIndex(pivot, leftBranch, rightBranch)
    }

    predicate SplitChildOfIndex(pivot: Key, newChildAddr: Address, newIndex: LinkedBranch)
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

  function EmptyLinkedBranch(root: Address) : (result: LinkedBranch)
    ensures result.WF()
  {
    LinkedBranch(root, EmptyDisk().ModifyDisk(root, Leaf([], [])))
  }

  datatype Path = Path(branch: LinkedBranch, key: Key, depth: nat)
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

    function Target() : (out: LinkedBranch)
      requires Valid()
      ensures out.WF()
      decreases depth
    {
      if 0 == depth
      then branch
      else Subpath().Target()
    }

    function Substitute(replacement: LinkedBranch) : (out: LinkedBranch)
      requires Valid()
    {
      LinkedBranch(branch.root, replacement.diskView)
    }

    predicate PathEquiv(otherKey: Key)
      requires Valid()
      decreases depth, 1
    {
      && branch.Root().Route(key) == branch.Root().Route(otherKey)
      && (0 < depth ==> Subpath().PathEquiv(otherKey))
    }
  }

  datatype Variables = Variables(branch: LinkedBranch)
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

  predicate Insert(v: Variables, v': Variables, lbl: TransitionLabel, path: Path, newTarget: LinkedBranch)
  {
    && lbl.InsertLabel?
    && v.WF()
    && path.Valid()
    && path.branch == v.branch
    && path.key == lbl.key
    && path.Target().Root().Leaf?
    && newTarget == path.Target().InsertLeaf(lbl.key, lbl.msg)
    && v'.branch == path.Substitute(newTarget)
  }

  predicate Append(v: Variables, v': Variables, lbl: TransitionLabel, path: Path, newTarget: LinkedBranch)
  {
    && lbl.AppendLabel?
    && v.WF()
    && path.Valid()
    && path.branch == v.branch
    && path.Target().Root() == Leaf([], [])
    && lbl.keys != []
    && |lbl.keys| == |lbl.msgs|
    && Keys.IsStrictlySorted(lbl.keys)

    && newTarget == path.Target().AppendToNewLeaf(lbl.keys, lbl.msgs)
    && path.key == newTarget.Root().keys[0]
    && path.PathEquiv(Last(newTarget.Root().keys))
    && v'.branch == path.Substitute(newTarget)
  }

  predicate Grow(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.InternalLabel?
    && v.WF()
    && v.branch.diskView.IsFresh({lbl.addr})
    && v'.branch == v.branch.Grow(lbl.addr)
  }

  predicate Split(v: Variables, v': Variables, lbl: TransitionLabel, 
    path: Path, pivot: Key, newTarget: LinkedBranch)
  {
    && lbl.InternalLabel?
    && v.WF()
    && path.Valid()
    && path.branch == v.branch
    && v.branch.diskView.IsFresh({lbl.addr})
    && path.Target().SplitChildOfIndex(pivot, lbl.addr, newTarget)
    && v'.branch == path.Substitute(newTarget)
  }

  // public:

  predicate Init(v: Variables)
  {
    && v.branch == EmptyLinkedBranch(v.branch.root)
  }

  datatype Step =
    | QueryStep()
    | InsertStep(path: Path, newTarget: LinkedBranch)
    | AppendStep(path: Path, newTarget: LinkedBranch)
    | GrowStep()
    | SplitStep(path: Path, pivot: Key, newTarget: LinkedBranch)

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case QueryStep() => Query(v, v', lbl)
      case InsertStep(path, newTarget) => Insert(v, v', lbl, path, newTarget)
      case AppendStep(path, newTarget) => Append(v, v', lbl, path, newTarget)
      case GrowStep() => Grow(v, v', lbl)
      case SplitStep(path, pivot, newTarget) => Split(v, v', lbl, path, pivot, newTarget)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }
}
