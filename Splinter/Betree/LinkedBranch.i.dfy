// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
 
include "../../lib/Base/KeyType.s.dfy"
include "../../Spec/Message.s.dfy"
include "../../lib/Base/Option.s.dfy"
include "../../lib/Base/Maps.i.dfy"
include "../../lib/Base/Sequences.i.dfy"
include "../../lib/Base/total_order_impl.i.dfy"
include "../Journal/GenericDisk.i.dfy"
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
  import KeysImpl = Lexicographic_Byte_Order_Impl
  import Keys = KeysImpl.Ord
  import P = PivotBranchMod

  type Address = GenericDisk.Address

  datatype Node = Index(pivots: seq<Key>, children: seq<Address>) | Leaf(keys: seq<Key>, msgs: seq<Message>)
  {
    predicate WF() {
      if Leaf? then 
        && |keys| > 0   // && can we ensure that there's more than 1
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

  // NOTE: use address instead of pointer here because the node is never nil,
  // there shouldn't be pivot entries without corresponding children
  datatype DiskView = DiskView(entries: map<Address, Node>) 
  {
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

    function Addresses() : set<Address>
    {
      set addr | addr in entries
    }

    predicate AllKeysAboveBound(addr: Address, pivots: seq<Key>, i: int)
      requires ValidAddress(addr)
    {
      && (0 <= i-1 < |pivots| ==> 
        && (forall key :: key in  GetKeys(addr) ==> Keys.lte(pivots[i-1], key)))
    }

    predicate AllKeysBelowBound(addr: Address, pivots: seq<Key>, i: int)
      requires ValidAddress(addr)
    {
      && (0 <= i < |pivots| ==>
        && (forall key :: key in GetKeys(addr) ==> Keys.lt(key, pivots[i])))
    }

    predicate ChildInRange(node: Node, i: nat) 
      requires node.Index?
      requires 0 <= i < |node.children|
    {
      var child := node.children[i];
      && (ValidAddress(child) ==> 
        && AllKeysAboveBound(child, node.pivots, i)
        && AllKeysBelowBound(child, node.pivots, i))
    }

    predicate NodeHasChildInRange(node: Node) {
      node.Index? ==>
        (forall idx:nat | idx < |node.children| :: ChildInRange(node, idx))
    }

    predicate EntriesChildInRange() {
      (forall addr | addr in entries :: NodeHasChildInRange(entries[addr]))
    }

    predicate EntriesWF() {
      && (forall addr | addr in entries :: entries[addr].WF())
    }
  
    predicate WF() {
      && EntriesWF()
      && NoDanglingAddress()
      && EntriesChildInRange()
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

  }

  function EmptyDisk() : DiskView {
    DiskView.DiskView(map[])
  }

  function {:opaque} MergeDiskViews(diskViews: seq<DiskView>) : (out: DiskView)
    // ensure result is sound -- keys and their values must come from one of these places
    ensures forall addr | addr in out.entries 
      :: (exists i :: 
            && 0 <= i < |diskViews|
            && addr in diskViews[i].entries
            && out.entries[addr] == diskViews[i].entries[addr]
      )
    // ensure result is complete -- result must contain all the keys
    ensures forall i | 0 <= i < |diskViews| :: diskViews[i].entries.Keys <= out.entries.Keys
    decreases |diskViews|
  { var out :=
      if |diskViews| == 0 then EmptyDisk()
      else diskViews[0].MergeDisk(MergeDiskViews(diskViews[1..]));
    reveal_MergeDiskViews();
    out
  }
 
  // This is the unit of interpretation: A LinkedBranch has enough info in it to interpret to a PivotBranch.Node
  datatype LinkedBranch = LinkedBranch(root: Address, diskView: DiskView)
  {
    predicate WF() {
      && diskView.WF()
      && diskView.ValidAddress(root)
    }

    predicate HasRoot() {
      && root in diskView.entries
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

    // return a sequence of all addressses starting from root
    // TODO: implement
    function AddressesFromRoot() : (addrs: seq<Address>)
      requires HasRoot()
      requires Acyclic()
      // requires ValidRanking(ranking)
      // ensures (forall addr | addr in addrs :: addr in diskView.entries)
      // decreases GetRank(ranking), 0
    {
      var node := Root();
      if node.Leaf? then (
        []
      ) else (
        []
      )
    }

  //   function AllKeys(ranking: Ranking) : (result: set<Key>)
  //     requires Acyclic()
  //     requires ValidRanking(ranking)
  //     ensures Root().Leaf? && 0 < |Root().keys| ==> result != {}
  //     ensures Root().Index? && 0 < |Root().pivots| ==> result != {}
  //     decreases GetRank(ranking), 0
  //   {
  //     var node := Root();
  //     if node.Leaf? then (
  //       var result := set k | k in node.keys;
  //       assert 0 < |node.keys| ==> node.keys[0] in result;
  //       result
  //     ) else (
  //       var pivotKeys := (set k | k in node.pivots);
  //       var indexKeys := (set i, k | 0 <= i < |node.children| && k in ChildAtIdx(i).AllKeys(ranking) :: k);
  //       var result := pivotKeys + indexKeys;
  //       assert 0 < |node.pivots| ==> node.pivots[0] in result;
  //       result
  //     )
  //   }
    
    function Query(key: Key) : (msg: Message)
    {
      // TODO: implement
      Update(NopDelta())
    }

    // Interpretation functions
    function I() : (out: P.Node)
      requires Acyclic()
      ensures Root().Index? <==> out.Index?
    {
      ILinkedBranchNode(TheRanking())
    }
  
    function ILinkedBranchNode(ranking: Ranking) : (out: P.Node)
      requires WF()
      requires ValidRanking(ranking)
      ensures Root().Index? <==> out.Index?
      ensures Root().Index? ==> Root().pivots == out.pivots
      ensures Root().Index? ==> |Root().children| == |out.children|      
      decreases GetRank(ranking), 1
    {
      var node := Root();
      if node.Leaf? 
      then P.Leaf(node.keys, node.msgs)
      else P.Index(node.pivots, IChildren(ranking))
    }

    function IChildren(ranking: Ranking) : (out: seq<P.Node>)
      requires WF()
      requires Root().Index?
      requires ValidRanking(ranking)
      decreases GetRank(ranking), 0
    {
      var numChildren := |Root().children|;
      seq(numChildren, i requires 0 <= i < numChildren => ChildAtIdx(i).ILinkedBranchNode(ranking))
    }

    lemma WFI(out: P.Node) 
    requires WF()
    requires Acyclic()
    requires out == I()
    ensures out.WF()
    {
      assume false;
    }
  }

  // Linked Branch State Machine:

  datatype Variables = Variables(linked: LinkedBranch) {
    predicate WF() {
      && linked.WF()
    }
  }

  predicate Query(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.QueryLabel?
    && v' == v
    // TODO: implement
  }

  predicate FilteredQuery(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.FilteredQueryLabel?
    && v' == v
    // TODO: implement
  }

  datatype Step =
    QueryStep 
  | FilteredQueryStep
  // | FlattenStep  // TODO: uncoment once we implement actual iterator

  datatype TransitionLabel =
    QueryLabel(key: Key, msg: Message)
  | FilteredQueryLabel(domain: Domain)
  // | FlattenLabel(flattened: FlattenedBranch)
  
  // public:

  predicate Init(v: Variables) {
    && v.WF()
  }

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case QueryStep() => Query(v, v', lbl)
      case FilteredQueryStep() => FilteredQuery(v, v', lbl)
      // case FlattenStep() => Flatten(v, v', lbl)
    }
  }
}
