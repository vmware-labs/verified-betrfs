// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
 
include "../../lib/Base/KeyType.s.dfy"
include "../../Spec/Message.s.dfy"
include "../../lib/Base/Option.s.dfy"
include "../../lib/Base/Maps.i.dfy"
include "../../lib/Base/Sets.i.dfy"
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
  import opened Sets
  import KeysImpl = Lexicographic_Byte_Order_Impl
  import Keys = KeysImpl.Ord
  import P = PivotBranchMod

  type Address = GenericDisk.Address

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

    function AllAddresses() : set<Address>
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

    function ReachableAddrs() : set<Address>
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
      && (Acyclic() ==> (ReachableAddrs() == diskView.AllAddresses()))
    }

    function QueryInternal(key: Key, ranking: Ranking) : (msg: Option<Message>)
      requires WF()
      requires ValidRanking(ranking)
      decreases GetRank(ranking)
      ensures ILinkedBranchNode(ranking).WF() ==> msg == ILinkedBranchNode(ranking).Query(key)
    {
      var node := Root();
      var r := node.Route(key);
      if node.Leaf? then (
        if r >= 0 && node.keys[r] == key
        then Some(node.msgs[r]) else None
      ) else (
        var result := ChildAtIdx(r+1).QueryInternal(key, ranking);
        result
      )
    }

    function Query(key: Key) : (msg: Option<Message>)
      requires WF()
      requires Acyclic()
      ensures I().WF() ==> msg == I().Query(key)
    {
      QueryInternal(key, TheRanking())
    }

    // Interpretation functions
    function I() : (out: P.Node)
      requires Acyclic()
      ensures Root().Index? <==> out.Index?
      ensures AllKeysInRange() ==> out.WF()
    {
      var ranking := TheRanking();
      var out := ILinkedBranchNode(ranking);
      assert AllKeysInRange() ==> out.WF() by {
        if AllKeysInRangeInternal(ranking) {
          ILinkedBranchNodeWF(ranking);
        }
      }
      out
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

    lemma AllKeysIsConsistentWithI(ranking: Ranking)
      requires WF()
      requires ValidRanking(ranking)
      ensures AllKeys(ranking) == ILinkedBranchNode(ranking).AllKeys()
      decreases GetRank(ranking)
    {
      var node := Root();
      if node.Leaf? {
      } else {
        var node' := ILinkedBranchNode(ranking);
        assert IChildren(ranking) == node'.children; // trigger

        forall k 
          ensures k in node'.AllKeys() <==> k in AllKeys(ranking)
        {
          if k in node'.AllKeys() {
            if k !in node'.pivots {
              var i :| 0 <= i < |node'.children| && k in node'.children[i].AllKeys();
              ChildAtIdx(i).AllKeysIsConsistentWithI(ranking);
              assert k in AllKeys(ranking);
            }
          } else if k in AllKeys(ranking) {
            if k !in node.pivots {
              var i :| 0 <= i < |node.children| && k in ChildAtIdx(i).AllKeys(ranking);
              var linked_child := ChildAtIdx(i);
              assert linked_child.ILinkedBranchNode(ranking) == node'.children[i];
              
              ChildAtIdx(i).AllKeysIsConsistentWithI(ranking);
              assert k in node'.AllKeys();
              assert false;
            }
          }
        }
      }
    }

    lemma ILinkedBranchNodeWF(ranking: Ranking)
      requires ILinkedBranchNode.requires(ranking)
      requires AllKeysInRangeInternal(ranking)
      ensures ILinkedBranchNode(ranking).WF()
      decreases GetRank(ranking)
    {
      var node := Root();
      var out := ILinkedBranchNode(ranking);
      
      if node.Index? {
        assert |out.pivots| == |out.children| - 1;
        assert Keys.IsStrictlySorted(out.pivots);

        forall i | 0 <= i < |IChildren(ranking)|
          ensures IChildren(ranking)[i].WF()
        {
          ChildAtIdx(i).ILinkedBranchNodeWF(ranking);
        }

        assert IChildren(ranking) == out.children; // trigger
        assert (forall i :: 0 <= i < |out.children| ==> out.children[i].WF());

        forall i | 0 <= i < |out.children|
          ensures i < |out.children|-1  ==> out.AllKeysBelowBound(i)
          ensures 0 < i ==> out.AllKeysAboveBound(i)
        {
          var child := out.children[i];
          var linked_child := ChildAtIdx(i);
          
          if 0 <= i < |out.children|-1 {
            assert AllKeysBelowBound(i, ranking);
          }

          if 0 < i < |out.children| {
            assert AllKeysAboveBound(i, ranking);
          }

          linked_child.AllKeysIsConsistentWithI(ranking);
        }
      }
    }
  }

  // Linked Branch State Machine:

  // datatype Variables = Variables(linked: LinkedBranch) {
  //   predicate WF() {
  //     && linked.WF()
  //   }
  // }

  // predicate Query(v: Variables, v': Variables, lbl: TransitionLabel)
  // {
  //   && v.WF()
  //   && lbl.QueryLabel?
  //   && v' == v
  //   // TODO: implement
  // }

  // predicate FilteredQuery(v: Variables, v': Variables, lbl: TransitionLabel)
  // {
  //   && v.WF()
  //   && lbl.FilteredQueryLabel?
  //   && v' == v
  //   // TODO: implement
  // }

  // datatype Step =
  //   QueryStep 
  // | FilteredQueryStep
  // // | FlattenStep  // TODO: uncoment once we implement actual iterator

  // datatype TransitionLabel =
  //   QueryLabel(key: Key, msg: Message)
  // | FilteredQueryLabel(domain: Domain)
  // // | FlattenLabel(flattened: FlattenedBranch)
  
  // // public:

  // predicate Init(v: Variables) {
  //   && v.WF()
  // }

  // predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  // {
  //   match step {
  //     case QueryStep() => Query(v, v', lbl)
  //     case FilteredQueryStep() => FilteredQuery(v, v', lbl)
  //     // case FlattenStep() => Flatten(v, v', lbl)
  //   }
  // }
}
