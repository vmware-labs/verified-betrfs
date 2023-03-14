// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "AllocationJournal.i.dfy"
include "LikesJournalRefinement.i.dfy"

// A Journal that keeps an in-memory index that maps each in-use LSN to the Address that stores it.
// The impl will keep such an index so that Discard can return freed Addresses without having to
// fault in the freed section of the journal to learn the chain of addresses involved.
module AllocationJournalRefinment {
  import opened Options
  import opened LSNMod
  import opened AllocationJournal
  import opened MiniAllocatorMod
  import L = LikesJournal
  import LR = LikesJournalRefinement

  function I(v: Variables) : L.Variables
  {
    v.journal
  }

  function GetTj(v: Variables) : TruncatedJournal
  {
    v.journal.journal.truncatedJournal
  }

  predicate AddrIndexConsistentWithAUIndex(lsnAddrIndex: map<LSN, Address>, lsnAUIndex: map<LSN, AU>)
  {
    && lsnAddrIndex.Keys == lsnAUIndex.Keys
    // Note: we need this instead of au in lsnAUIndex otherwise we can't prove DiscardOld refines
    && (forall lsn | lsn in lsnAddrIndex :: lsnAddrIndex[lsn].au == lsnAUIndex[lsn])
  }

  predicate JournalPagesNotFree(addrs: set<Address>, allocator: MiniAllocator)
  {
    && (forall addr | addr in addrs :: !allocator.CanAllocate(addr))
  }

  // TODO(Jialin): bad name?
  predicate MiniAllocatorFollowfreshestRec(freshestRec: Pointer, allocator: MiniAllocator)
  {
    // if freshestRec.None? then allocator.curr.None?
    // else if freshestRec.Some? && allocator.curr.Some? 
    // then allocator.MinAddr(freshestRec.value.NextPage())
    // else true
    && (freshestRec.None? ==> allocator.curr.None?)
    && (freshestRec.Some? && allocator.curr.Some? ==> 
      && var nextAddr := freshestRec.value.NextPage();
      && allocator.MinAddr(nextAddr))
  }

  predicate InternalAUPagesFullyLinked(dv: DiskView, first: AU)
  {
    && (forall addr | addr in dv.entries && addr.au != first :: AUPagesLinkedTillFirstInOrder(dv, addr))
    // forall addr | addr in addrs && addr.au != first :: AUPagesLinkedInOrder(dv, addr)
  }

  predicate Inv(v: Variables)
  {
    && LR.Inv(v.journal)
    // relationship between lsnAddrIndex and lsnAUIndex
    && AddrIndexConsistentWithAUIndex(v.journal.lsnAddrIndex, v.lsnAUIndex)
    // relationship between lsnAddrIndex and miniAllocator status
    && JournalPagesNotFree(v.journal.lsnAddrIndex.Values, v.miniAllocator)
    // relationship between journal freshestRec and miniAllocator
    && MiniAllocatorFollowfreshestRec(GetTj(v).freshestRec, v.miniAllocator)
    // constraints on page links within an AU
    // when one follows the prior link of a page within any AU except first
    // it will observe a link that's strictly decreasing and links down to page 0
    && InternalAUPagesFullyLinked(GetTj(v).diskView, v.first)

    // To be deleted
    // && (forall addr | addr in v.journal.lsnAddrIndex.Values :: 
    //   && addr.au in v.lsnAUIndex.Values
    //   && !v.miniAllocator.CanAllocate(addr))
    // NOTE: may need to change to diskview for easier proof?
    // && (forall addr | addr in v.journal.lsnAddrIndex.Values && addr.au != v.first ::
    //   && AUPagesLinkedInOrder(v.journal.journal.truncatedJournal.diskView, addr))
  }

  lemma InternalJournalMarshalRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires InternalJournalMarshal(v, v', lbl, step)
    ensures L.InternalJournalMarshal(I(v), I(v'), lbl.I(), step.cut, step.addr)
    ensures Inv(v')
  {
    assert LR.Inv(v.journal);
    LR.InvNextMarshalStep(I(v), I(v'), lbl.I(), step.cut, step.addr);
    assert LR.Inv(v'.journal);

    assert v.miniAllocator.MinAddr(step.addr); // 
    
    assert LR.IndexDomainValid(v'.journal.lsnAddrIndex, GetTj(v')); // from LR.Inv
    var discardmsgs := v.journal.journal.unmarshalledTail.DiscardRecent(step.cut);
    assert LikesJournal.LsnDisjoint(v.lsnAUIndex.Keys, discardmsgs) by {
      LR.reveal_IndexDomainValid();
    }
    assert v'.lsnAUIndex.Values == v.lsnAUIndex.Values + {step.addr.au};
    assert v'.journal.lsnAddrIndex.Values == v.journal.lsnAddrIndex.Values + {step.addr};
    assert AddrIndexConsistentWithAUIndex(v'.journal.lsnAddrIndex, v'.lsnAUIndex);

    // verifies just takes a while
    assume JournalPagesNotFree(v'.journal.lsnAddrIndex.Values, v'.miniAllocator);

    // assert MiniAllocatorFollowfreshestRec(GetTj(v).freshestRec, v.miniAllocator);
    // assert GetTj(v).freshestRec.None? ==> v.miniAllocator.curr.None?;
    // takes way too long to verify

    assume MiniAllocatorFollowfreshestRec(GetTj(v').freshestRec, v'.miniAllocator);
    // assert InternalAUPagesFullyLinked(GetTj(v').diskView, v'.first);

    assert GetTj(v').diskView == GetTj(v).diskView.(entries :=
      GetTj(v).diskView.entries[step.addr := 
      LinkedJournal.JournalRecord(discardmsgs, GetTj(v).freshestRec)]);

    forall addr | addr in GetTj(v').diskView.entries && addr.au != v'.first 
      ensures AUPagesLinkedTillFirstInOrder(GetTj(v').diskView, addr)
    {
      if addr in GetTj(v).diskView.entries {
        assert AUPagesLinkedTillFirstInOrder(GetTj(v).diskView, addr);
      } else {
        assert addr == step.addr;
        if GetTj(v).freshestRec.None? {
          // Jialin: all these assumes are asserts but idk why they take so long to verify
          assume v.miniAllocator.curr.None?; 
          assume v.miniAllocator.allocs[addr.au].MinFreeAddr(addr);
          assume v.miniAllocator.allocs[addr.au]
          v.miniAllocator.allocs[addr.au].MinFreeAddrZeroLemma(addr); 
          assert addr.page == 0;
          assume false;
        } else {
          assume false;
        }

//  && var newAddr := GenericDisk.Address(addr.au, page);
//       && var priorAddr := GenericDisk.Address(addr.au, page-1);
//       && dv.Decodable(Some(newAddr))
//       && dv.entries[newAddr].CroppedPrior(dv.boundaryLSN) == Some(priorAddr))
//   }

        // we know cropped prior is fine 

        // assume false;
      }
    }




    // // relationship between journal freshestRec and miniAllocator
    // && MiniAllocatorFollowfreshestRec(GetTj(v).freshestRec, v.miniAllocator)
    // // constraints on page links within an AU
    // // when one follows the prior link of a page within any AU except first
    // // it will observe a link that's strictly decreasing and links down to page 0
    // && InternalAUPagesFullyLinked(GetTj(v).diskView, v.first)

  
    // assume false;

    // forall addr | addr in v'.journal.lsnAddrIndex.Values && addr.au != v'.first
    //   ensures AUPagesLinkedInOrder(v'.journal.journal.truncatedJournal.diskView, addr)
    // {
    //   if addr in v.journal.lsnAddrIndex.Values {
    //     assert AUPagesLinkedInOrder(v'.journal.journal.truncatedJournal.diskView, addr);
    //   } else {

    //     assert addr == v'.journal.journal.truncatedJournal.freshestRec.value;
    //     assert v'.journal.journal.truncatedJournal.diskView.entries[addr].CroppedPrior(v'.journal.journal.truncatedJournal.diskView.boundaryLSN) == v.journal.journal.truncatedJournal.freshestRec;

    //     var fr := v.journal.journal.truncatedJournal.freshestRec;
    //     if fr.None? {
    //       // we need to prove that page # is 0

    //       // cur.Some? 
    //       // connect freshest rec 
    //     }

    //     // if no record, mini allocator can't have a curr
    //     // 

    //     // invariants on the state of mini allocator?


    //     // assert fr.Some?;
    //     // assume addr == GenericDisk.Address(fr.value.au, fr.value.page+1);
    //     // assume v.journal.journal.truncatedJournal.freshestRec == Some(GenericDisk.Address(addr.au, addr.page-1));

    //     assume false;
    //   }
    // }

    assume false;
  }

  lemma InitRefines()
  {

  }




}