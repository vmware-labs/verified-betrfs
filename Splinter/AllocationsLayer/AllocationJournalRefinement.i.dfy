// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "AllocationJournal.i.dfy"
include "../Journal/LikesJournalRefinement.i.dfy"

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
    && (forall addr | addr in addrs :: addr.WF() && !allocator.CanAllocate(addr))
  }

  predicate MiniAllocatorFollowfreshestRec(freshestRec: Pointer, allocator: MiniAllocator)
  {
    && (allocator.curr.Some? ==> 
      && freshestRec.Some?
      && freshestRec.value.au == allocator.curr.value)
  }

  predicate ValidFirstAU(dv: DiskView, lsnAUIndex: map<LSN, AU>, first: AU)
  {
    && dv.boundaryLSN in lsnAUIndex
    && lsnAUIndex[dv.boundaryLSN] == first
  }

  predicate ContiguousLSNs(lsn1: LSN, lsn2: LSN, lsn3: LSN, lsnAUIndex: map<LSN, AU>)
  {
    ( && lsn1 <= lsn2 <= lsn3 
      && lsn1 in lsnAUIndex 
      && lsn3 in lsnAUIndex
      && lsnAUIndex[lsn1] == lsnAUIndex[lsn3]) 
    ==> 
    ( && lsn2 in lsnAUIndex
      && lsnAUIndex[lsn2] == lsnAUIndex[lsn1])
  }

  predicate AUsHoldContiguousLSNs(lsnAUIndex: map<LSN, AU>)
  {
    && (forall lsn1, lsn2, lsn3 :: ContiguousLSNs(lsn1, lsn2, lsn3, lsnAUIndex))
  }

  predicate {:opaque} LikesJournalInv(v: Variables)
  {
    && LR.Inv(v.journal)
  }

  predicate Inv(v: Variables)
  {
    && v.WF()
    && LikesJournalInv(v)
    && AddrIndexConsistentWithAUIndex(v.journal.lsnAddrIndex, v.lsnAUIndex)
    && JournalPagesNotFree(v.journal.lsnAddrIndex.Values, v.miniAllocator)
    && MiniAllocatorFollowfreshestRec(GetTj(v).freshestRec, v.miniAllocator)

    && AUsHoldContiguousLSNs(v.lsnAUIndex)
    && (GetTj(v).freshestRec.Some? ==> ValidFirstAU(GetTj(v).diskView, v.lsnAUIndex, v.first))
    && (GetTj(v).freshestRec.Some? ==> InternalAUPagesFullyLinked(GetTj(v).diskView, v.first))
    // constraints on page links within an AU
    // when one follows the prior link of a page within any AU except first
    // it will observe a link that's strictly decreasing and links down to page 0
  }

  lemma InternalJournalMarshalRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires InternalJournalMarshal(v, v', lbl, step)
    ensures L.InternalJournalMarshal(I(v), I(v'), lbl.I(), step.cut, step.addr)
    ensures LikesJournalInv(v')
  {
    reveal_LikesJournalInv();
    assert LR.Inv(v.journal);
    if step.addr in v.journal.lsnAddrIndex.Values {
      assert false;
    }
    LR.InvNextMarshalStep(I(v), I(v'), lbl.I(), step.cut, step.addr);
  }

  lemma AUPagesLinkedTillFirstInOrderInc(dv: DiskView, addr: Address, prior: Address)
    requires addr == prior.NextPage()
    requires dv.Decodable(Some(addr))
    requires dv.entries[addr].CroppedPrior(dv.boundaryLSN) == Some(prior)
    requires AUPagesLinkedTillFirstInOrder(dv, prior)
    ensures AUPagesLinkedTillFirstInOrder(dv, addr)
  {
  }

  lemma InternalJournalMarshalPreservesContiguousLSNs(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires LikesJournalInv(v')
    requires InternalJournalMarshal(v, v', lbl, step)
    ensures AUsHoldContiguousLSNs(v'.lsnAUIndex)
  { 
    var discardmsgs := v.journal.journal.unmarshalledTail.DiscardRecent(step.cut);
    assert LikesJournal.LsnDisjoint(v.lsnAUIndex.Keys, discardmsgs) by {
      reveal_LikesJournalInv();
      LR.reveal_IndexDomainValid();
    }

    var lsnAUIndex := v'.lsnAUIndex;
    var firstMarshalled := discardmsgs.seqStart;

    forall lsn1, lsn2, lsn3
    ensures ContiguousLSNs(lsn1, lsn2, lsn3, lsnAUIndex)
    {
      if (&& lsn1 <= lsn2 <= lsn3 
        && lsn1 in lsnAUIndex 
        && lsn3 in lsnAUIndex
        && lsnAUIndex[lsn1] == lsnAUIndex[lsn3]) {
        if firstMarshalled <= lsn2 {
          assert 
            && discardmsgs.Contains(lsn2) 
            && discardmsgs.Contains(lsn3) 
          by {
            reveal_LikesJournalInv();
            LR.reveal_IndexDomainValid();
          }
          assert lsn2 in lsnAUIndex;
          assert lsnAUIndex[lsn2] == lsnAUIndex[lsn1];
        } else if firstMarshalled <= lsn3 {
          if v.miniAllocator.curr.Some? {
            assert GetTj(v).freshestRec.Some?;
            var lastLSN := GetTj(v).SeqEnd() - 1;            
            assert lastLSN in v.journal.lsnAddrIndex by { reveal_LikesJournalInv(); }

            assert v.journal.lsnAddrIndex[lastLSN] == GetTj(v).freshestRec.value by {  reveal_LikesJournalInv(); }
            assert lsnAUIndex[lastLSN] == lsnAUIndex[firstMarshalled];
            assert discardmsgs.Contains(lsn3) by {
              reveal_LikesJournalInv();
              LR.reveal_IndexDomainValid();
            }
            assert lsnAUIndex[firstMarshalled] == lsnAUIndex[lsn3];
            assert lsnAUIndex[lsn3] == lsnAUIndex[lsn1];
            assert ContiguousLSNs(lsn1, lsn2, lastLSN, v.lsnAUIndex);
            assert lsn2 in lsnAUIndex;
            assert lsnAUIndex[lsn2] == lsnAUIndex[lsn1]; 
          } else {
            // lsn1 & lsn3 has the same AU, so mini allocator curr must be a some
            assert discardmsgs.Contains(lsn3) by {
              reveal_LikesJournalInv();
              LR.reveal_IndexDomainValid();
            }
            assert lsnAUIndex[lsn3] == step.addr.au;
            var page := v.journal.lsnAddrIndex[lsn1];
            assert !v.miniAllocator.CanAllocate(page); // meow 
            assert lsnAUIndex[lsn1] != step.addr.au; 
            assert false;
          }
        } else {
          assert ContiguousLSNs(lsn1, lsn2, lsn3, v.lsnAUIndex);
        }
      } 
    }
  }

  lemma InternalJournalMarshalInv(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires LikesJournalInv(v')
    requires InternalJournalMarshal(v, v', lbl, step)
    ensures Inv(v')
  {
    assert v.WF();
    var discardmsgs := v.journal.journal.unmarshalledTail.DiscardRecent(step.cut);
    assert LikesJournal.LsnDisjoint(v.lsnAUIndex.Keys, discardmsgs) by {
      reveal_LikesJournalInv();
      LR.reveal_IndexDomainValid();
    }
    assert v'.lsnAUIndex.Values == v.lsnAUIndex.Values + {step.addr.au};
    assert v'.journal.lsnAddrIndex.Values == v.journal.lsnAddrIndex.Values + {step.addr};
    assert v'.WF() by { reveal_LikesJournalInv(); }

    assert AddrIndexConsistentWithAUIndex(v'.journal.lsnAddrIndex, v'.lsnAUIndex);
    forall addr | addr in v'.journal.lsnAddrIndex.Values
      ensures !v'.miniAllocator.CanAllocate(addr)
    {
      if addr == step.addr {
        assert !v'.miniAllocator.CanAllocate(addr);
      } else {
        assert !v.miniAllocator.CanAllocate(addr);
      }
    }

    assert JournalPagesNotFree(v'.journal.lsnAddrIndex.Values, v'.miniAllocator);
    InternalJournalMarshalPreservesContiguousLSNs(v, v', lbl, step);

    assert MiniAllocatorFollowfreshestRec(GetTj(v).freshestRec, v.miniAllocator);
    assert MiniAllocatorFollowfreshestRec(GetTj(v').freshestRec, v'.miniAllocator);

    forall addr | addr in GetTj(v').diskView.entries && addr.au != v'.first
      ensures AUPagesLinkedTillFirstInOrder(GetTj(v').diskView, addr)
    {
      if addr == step.addr {
        assert GetTj(v').diskView.entries[step.addr].CroppedPrior(GetTj(v').diskView.boundaryLSN) == GetTj(v).freshestRec;
        assert ValidNextJournalAddr(v, step.addr);
        
        if v.miniAllocator.curr.None? {
          assert AUPagesLinkedTillFirstInOrder(GetTj(v').diskView, addr);
        } else {
          assert GetTj(v).freshestRec.Some?;
          assert addr == GetTj(v).freshestRec.value.NextPage();
          assert GetTj(v').diskView.Decodable(Some(addr));

          assert AUPagesLinkedTillFirstInOrder(GetTj(v).diskView, GetTj(v).freshestRec.value);
          AUPagesLinkedTillFirstInOrderInc(GetTj(v').diskView, addr, GetTj(v).freshestRec.value);
        }
      } else {
        reveal_LikesJournalInv();
        assert AUPagesLinkedTillFirstInOrder(GetTj(v).diskView, addr);
      }
    }
  }

  lemma DiscardOldRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires DiscardOld(v, v', lbl)
    ensures L.DiscardOld(I(v), I(v'), lbl.I())
    ensures LikesJournalInv(v')
  {
    reveal_LikesJournalInv();
    assert L.NextStep(I(v), I(v'), lbl.I(), L.DiscardOldStep);
    LR.InvNext(I(v), I(v'), lbl.I());
  }

  lemma SmallerPageHasSmallerLSNs(dv: DiskView, prior: Address, later: Address)
    requires dv.WF()
    requires prior.au == later.au
    requires prior.page < later.page
    requires AUPagesLinkedTillFirstInOrder(dv, later)
    ensures prior in dv.entries
    ensures later in dv.entries
    ensures dv.entries[prior].messageSeq.seqEnd <= dv.entries[later].messageSeq.seqStart
    decreases later.page
  {
    var priorAddr := GenericDisk.Address(later.au, later.page-1);
    if priorAddr == prior {
      assert dv.entries[prior].messageSeq.seqEnd <= dv.entries[later].messageSeq.seqStart;
    } else {
      SmallerPageHasSmallerLSNs(dv, prior, dv.entries[later].CroppedPrior(dv.boundaryLSN).value);
    }
  }

  lemma DiscardOldInv(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires LikesJournalInv(v')
    requires DiscardOld(v, v', lbl)
    ensures Inv(v')
  {
    assert v'.WF() by { reveal_LikesJournalInv(); }
    assert AddrIndexConsistentWithAUIndex(v'.journal.lsnAddrIndex, v'.lsnAUIndex);
    assert JournalPagesNotFree(v'.journal.lsnAddrIndex.Values, v'.miniAllocator) by { reveal_LikesJournalInv(); }

    if GetTj(v).freshestRec.Some? && GetTj(v').freshestRec.None? {
      assert GetTj(v).freshestRec.value in v.journal.lsnAddrIndex.Values by { reveal_LikesJournalInv(); }
      assert v'.journal.lsnAddrIndex == map[] by { reveal_LikesJournalInv(); }
    }
    assert MiniAllocatorFollowfreshestRec(GetTj(v').freshestRec, v'.miniAllocator);

    forall lsn1, lsn2, lsn3
    ensures ContiguousLSNs(lsn1, lsn2, lsn3, v'.lsnAUIndex)
    {
      if (&& lsn1 <= lsn2 <= lsn3 
        && lsn1 in v'.lsnAUIndex 
        && lsn3 in v'.lsnAUIndex
        && v'.lsnAUIndex[lsn1] == v'.lsnAUIndex[lsn3]) { 
        assert ContiguousLSNs(lsn1, lsn2, lsn3, v.lsnAUIndex); // trigger
      }
    }
    assert AUsHoldContiguousLSNs(v'.lsnAUIndex);

    if GetTj(v').freshestRec.Some? {
      assert ValidFirstAU(GetTj(v').diskView, v'.lsnAUIndex, v'.first) by {
        reveal_LikesJournalInv(); 
        LR.reveal_IndexDomainValid();
      }

      forall addr | addr in GetTj(v').diskView.entries && addr.au != v'.first 
        ensures AUPagesLinkedTillFirstInOrder(GetTj(v').diskView, addr) 
      {
        if addr.au == v.first {
          assert v.first != v'.first;
          var lsn :| lsn in v'.journal.lsnAddrIndex && v'.journal.lsnAddrIndex[lsn] == addr;
          assert ContiguousLSNs(GetTj(v).diskView.boundaryLSN, lbl.startLsn, lsn, v.lsnAUIndex);
          assert false;
        } else {
          assert AUPagesLinkedTillFirstInOrder(GetTj(v).diskView, addr);

          var lsn :| lsn in v'.journal.lsnAddrIndex && v'.journal.lsnAddrIndex[lsn] == addr;
          assert LR.IndexKeysMapToValidEntries(v'.journal.lsnAddrIndex, GetTj(v')) by { reveal_LikesJournalInv(); }
          LR.InstantiateIndexKeysMapToValidEntries(v'.journal.lsnAddrIndex, GetTj(v'), lsn);
          // assert GetTj(v').diskView.entries[addr].ContainsLSN(lsn);
          // assert GetTj(v).diskView.entries[addr].ContainsLSN(lsn);

          forall page:nat | 0 <= page < addr.page
            ensures 
              && var priorAddr := GenericDisk.Address(addr.au, page);
              && priorAddr in GetTj(v').diskView.entries
              && GetTj(v').diskView.entries[priorAddr.NextPage()].CroppedPrior(lbl.startLsn) == Some(priorAddr)
          {
            var priorAddr := GenericDisk.Address(addr.au, page);
            assert priorAddr in GetTj(v).diskView.entries;
            assert priorAddr in v.journal.lsnAddrIndex.Values by { reveal_LikesJournalInv(); }

            var priorAddrLsn :| priorAddrLsn in v.journal.lsnAddrIndex && v.journal.lsnAddrIndex[priorAddrLsn] == priorAddr;
            assert LR.IndexKeysMapToValidEntries(v.journal.lsnAddrIndex, GetTj(v)) by { reveal_LikesJournalInv(); }
            LR.InstantiateIndexKeysMapToValidEntries(v.journal.lsnAddrIndex, GetTj(v), priorAddrLsn);
            // assert GetTj(v).diskView.entries[priorAddr].ContainsLSN(priorAddrLsn);

            if priorAddrLsn <= lbl.startLsn {
              SmallerPageHasSmallerLSNs(GetTj(v).diskView, priorAddr, addr);
              assert priorAddrLsn <= lsn;
              assert ContiguousLSNs(priorAddrLsn, lbl.startLsn, lsn, v.lsnAUIndex);
              assert false;
            }
            assert priorAddrLsn > lbl.startLsn;
            assert priorAddr in GetTj(v').diskView.entries;
          }
        }
      }
      assert InternalAUPagesFullyLinked(GetTj(v').diskView, v'.first);
    }
  }
 
  lemma InitRefines(v: Variables, journal: TruncatedJournal, first: AU)
    requires Init(v, journal, first)
    ensures LikesJournalInv(v)
    ensures LikesJournal.Init(I(v), journal)
  {
    LR.InvInit(v.journal, journal);
    reveal_LikesJournalInv();
  }

  lemma InvInit(v: Variables, journal: TruncatedJournal, first: AU)
    requires Init(v, journal, first)
    requires LikesJournalInv(v)
    ensures Inv(v)
  {
    assert v.WF();
    assert MiniAllocatorFollowfreshestRec(GetTj(v).freshestRec, v.miniAllocator);

    // assert JournalPagesNotFree(v.journal.lsnAddrIndex.Values, v.miniAllocator);

    forall addr | addr in v.journal.lsnAddrIndex.Values
      // ensures addr.WF()
      ensures !v.miniAllocator.CanAllocate(addr)
    {
      assert addr.au !in v.miniAllocator.allocs;
      // we started to slap an address in WF
      // assume addr.WF();
    }

    // assert AddrIndexConsistentWithAUIndex(v.journal.lsnAddrIndex, v.lsnAUIndex);


    // && AUsHoldContiguousLSNs(v.lsnAUIndex)
    // && (GetTj(v).freshestRec.Some? ==> ValidFirstAU(GetTj(v).diskView, v.lsnAUIndex, v.first))
    // && (GetTj(v).freshestRec.Some? ==> InternalAUPagesFullyLinked(GetTj(v).diskView, v.first))

    assume false;
    // reveal_IndexDomainValid();
    // reveal_IndexKeysMapToValidEntries();
    // LinkedJournalRefinement.BuildTightIsAwesome(tj.diskView, tj.freshestRec);
    // var tightTj := tj.BuildTight();
    // if tightTj.freshestRec.Some? {
    //   BuildLsnAddrIndexDomainValid(tightTj.diskView, tightTj.freshestRec);
    // }
    // BuildLsnAddrIndexRangeValid(tightTj.diskView, tightTj.freshestRec,tightTj.SeqEnd());
    // BuildLsnAddrIndexGivesRepresentation(tightTj);
    // BuildTightGivesRepresentation(tj.diskView, tj.freshestRec);
    // RepresentationIgnoresBuildTight(tj.diskView, tj.freshestRec, tj.freshestRec);
    // BuildLsnAddrIndexIgnoresBuildTight(tj.diskView, tj.freshestRec, tj.freshestRec);
  }

  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
    ensures LikesJournal.Next(I(v), I(v'), lbl.I())
  {
    assert Inv(v);
    // InvNext(v, v', lbl);
    var step: Step :| NextStep(v, v', lbl, step);
    match step {
      case InternalMiniAllocatorFillStep() => { assume false; }
      case InternalMiniAllocatorPruneStep() => { assume false; }
      case DiscardOldStep() => {
        assert DiscardOld(v, v', lbl);
        DiscardOldRefines(v, v', lbl);
        DiscardOldInv(v, v', lbl);
        assert LikesJournal.NextStep(I(v), I(v'), lbl.I(), step.I());
      }
      case InternalJournalMarshalStep(cut, addr) => {
        assert InternalJournalMarshal(v, v', lbl, step);
        InternalJournalMarshalRefines(v, v', lbl, step);
        InternalJournalMarshalInv(v, v', lbl, step);
        assert LikesJournal.NextStep(I(v), I(v'), lbl.I(), step.I());
      }
      case InternalNoOpStep() => {
        assert LikesJournal.NextStep(I(v), I(v'), lbl.I(), step.I());
      }
      case _ => {
        assert OnlyAdvanceLikesJournal(v, v', lbl, step);
        reveal_LikesJournalInv();
        assert LikesJournal.NextStep(I(v), I(v'), lbl.I(), step.I());
        LR.InvNext(I(v), I(v'), lbl.I());
        assert Inv(v');
      }
    }
  }
}