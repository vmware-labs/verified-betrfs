// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Journal/GenericDisk.i.dfy"
include "LinkedBranch.i.dfy"

module BranchesMod {
	import opened KeyType
	import opened ValueMessage
  import opened Maps
	import opened Sequences
	import opened LinkedBranchMod
  import D = GenericDisk

  function EmptyBranches() : Branches
  {
    Branches({}, DiskView.DiskView(map[]))
  }

	// Track the branches as branchroot and a single diskView
	// We can construct LinkedBranch from each tree and the diskView
	datatype Branches = Branches(roots: set<Address>, diskView: DiskView) 
	{
		predicate WF() {
			&& diskView.WF() // ensures all nodes are connected
			&& (forall root | root in roots :: diskView.ValidAddress(root))
      && (forall root | root in roots :: GetBranch(root).Acyclic())
      && (forall root | root in roots :: GetBranch(root).AllKeysInRange())
      && BranchesDisjoint()
		}

    predicate BranchesDisjoint()
    {
      && (forall r1, r2 | r1 in roots && r2 in roots && r1 != r2 :: 
        GetBranch(r1).ReachableAddrs() !! GetBranch(r2).ReachableAddrs())
    }

		predicate ValidBranch(addr: Address)
		{
			addr in roots
		}

		function GetBranch(addr: Address) : (branch: LinkedBranch)
      requires ValidBranch(addr)
		{
      LinkedBranch(addr, diskView)
		}

		function Query(key: Key, buffers: seq<Address>) : Message
      requires WF()
      requires (forall addr | addr in buffers :: ValidBranch(addr))
		{
			if buffers == [] then Update(NopDelta())
      else (
				var branch := GetBranch(Last(buffers));
        var msg := if branch.Query(key).Some? then branch.Query(key).value else Update(NopDelta());
				Merge(Query(key, DropLast(buffers)), msg)
			)
		}

    function AddBranch(branch: LinkedBranch) : (out: Branches)
      requires WF()
      requires branch.Acyclic()
      requires branch.AllKeysInRange()
      requires branch.TightDiskView()
      requires diskView.IsFresh(branch.ReachableAddrs())
    {
      Branches(roots + {branch.root}, diskView.MergeDisk(branch.diskView))
    }
    
    function RemoveBranch(root: Address) : (out: Branches)
      requires WF()
      requires ValidBranch(root)
    {
      var branchDisk := DiskView(MapRestrict(diskView.entries, GetBranch(root).ReachableAddrs()));
      Branches(roots - {root}, diskView.RemoveDisk(branchDisk))
    }

    // TODO: why we needed this again lol we will see if we can use it for 
    // ah it's easier to put things togther this way I think
    // like a compose rankings thing
    function GetTightBranch(addr: Address) : (branch: LinkedBranch)
      requires WF()
      requires ValidBranch(addr)
      ensures branch.WF()
      ensures branch.Acyclic()
    {
      var branch := GetBranch(addr);
      var tightDisk := DiskView(MapRestrict(diskView.entries, branch.ReachableAddrs()));
      var tightBranch := LinkedBranch(addr, tightDisk);

      assert tightDisk.WF() by {
        forall addr | addr in tightDisk.entries 
          ensures tightDisk.NodeHasValidChildAddress(tightDisk.entries[addr])
        {
          branch.ReachableAddrClosed(branch.TheRanking(), addr);
        }
      }

      assert tightBranch.Acyclic() by {
        assert tightBranch.ValidRanking(branch.TheRanking());
      }

      tightBranch
    }

    lemma AddBranchWF(branch: LinkedBranch) 
      requires AddBranch.requires(branch)
      ensures AddBranch(branch).WF()
    {
      // see if this can help us
      // GetTightBranch

      // assert (exists ranking | (forall r | r in roots :: MapsAgree(ranking, GetBranch(r).))
      
      
      
      // )
      // var  := AddBranch(branch);

      

      // let's merge it 
      // var ranking :| (forall r | r in roots :: MapsAgree(ranking, GetBranch(r).TheRanking()));
      
      // GetBranch(r).ValidRanking(ranking));
      //diskView.ValidRanking(ranking) && (forall r | r in roots :: r in ranking); 


      assume false;

      // forall addr | addr in ranking 
      //   && addr in entries 




      //  assert forall addr | addr in diskView.entries :: 
      //       && addr in newBranches.diskView.entries 
      //       && diskView.entries[addr] == newBranches.diskView.entries[addr];
      // assert newBranches.diskView.WF();
      // var newRanking := 

      // forall root | root in newBranches.roots
      //   ensures newBranches.GetBranch(root).Acyclic()
      // {
        // maybe before this step what we want to prove is that 
        // ValidRanking


        // is it easier if I show that each is disjoint?
        // maybe I am dying percisely bc I don't have a disjoint clause
        
      //   if root == branch.root {
      //     assume false;
      //   } else {
      //     var b := GetBranch(root);
      //     var b' := newBranches.GetBranch(root);

      //     var ranking := b.TheRanking();
      //     assert b.ValidRanking(ranking);
      //     assert b.diskView == diskView;

      //     // valid ranking 
      //     // assert forall r | r in ranking :: r in diskView.entries 
    
      //     forall addr | addr in ranking && addr in newBranches.diskView.entries 
      //       ensures newBranches.diskView.NodeChildrenRespectsRank(ranking, addr)
      //     {
      //       assert addr in diskView.entries;
      //       // if addr in diskView.entries 
          
      //       // assert diskView.NodeChildrenRespectsRank(ranking, addr);
      //       assume false;
      //     }


        

      //     assert b'.ValidRanking(ranking);
      //     assert b'.Acyclic();
          


      //     assume false;

      //     assert newBranches.GetBranch(root).ValidRanking(GetBranch(root).TheRanking());
      //     assert newBranches.GetBranch(root).Acyclic();
      //     // GetBranch()
      //   }

      //   // assume false;
      // }

      // forall root | root in newBranches.roots
      //   ensures newBranches.GetBranch(root).AllKeysInRange()
      // {
      //   assume false;
      // }
    }
     
     lemma RemoveBranchWF(root: Address) 
      requires RemoveBranch.requires(root)
      ensures RemoveBranch(root).WF() 
    {
      assume false;

    }
	}
}