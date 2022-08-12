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
      && EntriesChildInRange()
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
      && ValidAddress(child)
      && AllKeysAboveBound(child, node.pivots, i)
      && AllKeysBelowBound(child, node.pivots, i)
    }

    predicate NodeHasChildInRange(node: Node) {
      node.Index? ==>
        (forall idx:nat | idx < |node.children| :: ChildInRange(node, idx))
    }

    predicate EntriesChildInRange() {
      (forall addr | addr in entries :: NodeHasChildInRange(entries[addr]))
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

    // I guess the benefit is that we do like to be able to refine it so that we can show 
    // what are we using this for? the all keys guarantee as a tree property it

    // we want to expose something with range?

    // function AllKeys(ranking: Ranking) : (result: set<Key>)
    //   requires WF()
    //   requires ValidRanking(ranking)
    //   ensures Root().Leaf? && 0 < |Root().keys| ==> result != {}
    //   ensures Root().Index? && 0 < |Root().pivots| ==> result != {}
    //   // ensures result == ILinkedBranchNode(ranking).AllKeys()
    //   decreases GetRank(ranking), 0
    // {
    //   var node := Root();
    //   if node.Leaf? then (
    //     var result := set k | k in node.keys;
    //     assert 0 < |node.keys| ==> node.keys[0] in result;
    //     result
    //   ) else (
    //     // assume false;
    //     var pivotKeys := (set k | k in node.pivots);
    //     var indexKeys := (set i, k | 0 <= i < |node.children| && k in ChildAtIdx(i).AllKeys(ranking) :: k);

    //     // assert (forall i | 0 <= i < |node.children| :: ChildAtIdx(i).AllKeys(ranking) == ChildAtIdx(i).I().AllKeys()) by {
    //     //   assume false;
    //     // }
      
    //     var result := pivotKeys + indexKeys;
    //     assert 0 < |node.pivots| ==> node.pivots[0] in result;
    //     result
    //   )
    // }
    
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

    lemma ILinkedBranchNodeWF(ranking: Ranking)
      requires ILinkedBranchNode.requires(ranking)
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

        forall i | 0 <= i < |out.children|-1 
          ensures out.AllKeysBelowBound(i)
        {
          var child := out.children[i];
          if child.Leaf? {
            assert child.AllKeys() == Set(child.keys);
            assert diskView.ChildInRange(node, i);  // trigger
          } else {
            var pivotKeys := Set(child.pivots);
            var indexKeys := (set i, k | 0 <= i < |child.children| && k in child.children[i].AllKeys() :: k);
            assert child.AllKeys() == pivotKeys + indexKeys;

            var linked_child := ChildAtIdx(i);
            assert linked_child.ILinkedBranchNode(ranking) == child;
            
            forall k | k in child.AllKeys()
            ensures Keys.lt(k, node.pivots[i]) 
            {
              assert diskView.ChildInRange(Root(), i); // trigger
              
              if k in indexKeys {
                var j :| 0 <= j < |child.children| && k in child.children[j].AllKeys();
                assert child.WF();
                if child.Leaf? {
                  // also don't know anything here
                  assume false;
                } else {
                  if j < |child.pivots| {
                    assert child.AllKeysBelowBound(j);
                    assert Keys.lt(k, child.pivots[j]);
                    assert Keys.lt(child.pivots[j], out.pivots[i]);
                    Keys.lteTransitiveForall();
                    assert Keys.lt(k, out.pivots[i]);
                  } else {
                    // we don't anything here
                    assume false;
                  }
                }
              } else {
                assert Keys.lt(k, node.pivots[i]);
              }
            }
            assert forall key :: key in child.AllKeys() ==> Keys.lt(key, node.pivots[i]);
          }
        }
        assume (forall i :: 0 < i < |out.children|   ==> out.AllKeysAboveBound(i));
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
