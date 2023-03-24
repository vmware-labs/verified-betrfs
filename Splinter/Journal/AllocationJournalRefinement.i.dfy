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
    && (forall addr | addr in addrs :: addr.WF() && !allocator.CanAllocate(addr))
  }

  predicate MiniAllocatorFollowfreshestRec(freshestRec: Pointer, allocator: MiniAllocator)
  {
    && (allocator.curr.Some? ==> 
      && freshestRec.Some?
      && freshestRec.value.au == allocator.curr.value)
  }

  predicate InternalAUPagesFullyLinked(dv: DiskView, first: AU)
  {
    && (forall addr | addr in dv.entries && addr.au != first :: AUPagesLinkedTillFirstInOrder(dv, addr))
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
    // && PriorPagesContainSmallerLSNs(GetTj(v).diskView)

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

    var lsnAUIndex := v'.lsnAUIndex;
    forall lsn1, lsn2, lsn3
    ensures ContiguousLSNs(lsn1, lsn2, lsn3, lsnAUIndex)
    {
      if (&& lsn1 <= lsn2 <= lsn3 
      && lsn1 in lsnAUIndex 
      && lsn3 in lsnAUIndex
      && lsnAUIndex[lsn1] == lsnAUIndex[lsn3])
      {
        var firstMarshalled := discardmsgs.seqStart;
        if firstMarshalled <= lsn1 {
          assert 
            && discardmsgs.Contains(lsn1)
            && discardmsgs.Contains(lsn3)
            && discardmsgs.Contains(lsn2) by {
            reveal_LikesJournalInv();
            LR.reveal_IndexDomainValid();
          }
          assert lsn2 in lsnAUIndex;
          assert lsnAUIndex[lsn2] == lsnAUIndex[lsn1];
        } else if firstMarshalled <= lsn2 {
          assert 
            && discardmsgs.Contains(lsn2) 
            && discardmsgs.Contains(lsn3) by {
            reveal_LikesJournalInv();
            LR.reveal_IndexDomainValid();
          }
          assert lsn2 in lsnAUIndex;
          assert lsnAUIndex[lsn2] == lsnAUIndex[lsn1];
        } else if firstMarshalled <= lsn3 {
          if v.miniAllocator.curr.Some? {
            if GetTj(v).freshestRec.None? {
              assert false;
            } else {
              var e := firstMarshalled - 1;
              assert e in v.journal.lsnAddrIndex by {
                reveal_LikesJournalInv();
                // LR.reveal_IndexDomainValid();
              }
              // TODO(Jialin) takes forever
              assume v.journal.lsnAddrIndex[e] == GetTj(v).freshestRec.value; 
              assert lsnAUIndex[e] == lsnAUIndex[firstMarshalled];
              assert discardmsgs.Contains(lsn3) by {
                reveal_LikesJournalInv();
                LR.reveal_IndexDomainValid();
              }
              assert lsnAUIndex[firstMarshalled] == lsnAUIndex[lsn3];
              assert lsnAUIndex[lsn3] == lsnAUIndex[lsn1];
              assert ContiguousLSNs(lsn1, lsn2, e, v.lsnAUIndex);
              assert lsn2 in lsnAUIndex;
              assert lsnAUIndex[lsn2] == lsnAUIndex[lsn1]; 
            }
          } else {
            // lsn1 & lsn3 has the same AU, so mini allocator curr must be a some
            assert discardmsgs.Contains(lsn3) by {
              reveal_LikesJournalInv();
              LR.reveal_IndexDomainValid();
            }
            assert lsnAUIndex[lsn3] == step.addr.au;
            var page := v.journal.lsnAddrIndex[lsn1];
            assert !v.miniAllocator.CanAllocate(page);
            assert lsnAUIndex[lsn1] != step.addr.au; 
            assert false;
          }
        } else {
          assert ContiguousLSNs(lsn1, lsn2, lsn3, v.lsnAUIndex);
        }
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

  lemma DiscardOldInv(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires LikesJournalInv(v')
    requires DiscardOld(v, v', lbl)
    ensures Inv(v')
  {
    assert v'.WF() by { reveal_LikesJournalInv(); }
    assert AddrIndexConsistentWithAUIndex(v'.journal.lsnAddrIndex, v'.lsnAUIndex);
    assert JournalPagesNotFree(v'.journal.lsnAddrIndex.Values, v'.miniAllocator) by { reveal_LikesJournalInv(); }
    // assert PriorPagesContainSmallerLSNs(GetTj(v').diskView);

    if GetTj(v).freshestRec.Some? && GetTj(v').freshestRec.None? {
      assert GetTj(v).freshestRec.value in v.journal.lsnAddrIndex.Values by { reveal_LikesJournalInv(); }
      assert v'.journal.lsnAddrIndex == map[] by { reveal_LikesJournalInv(); }
    }
    assert MiniAllocatorFollowfreshestRec(GetTj(v').freshestRec, v'.miniAllocator);
    
    if GetTj(v').freshestRec.Some? {
      assert lbl.startLsn in v.journal.lsnAddrIndex by {
        LR.reveal_IndexDomainValid();
        reveal_LikesJournalInv(); 
      }
    }
    assert (GetTj(v').freshestRec.Some? ==> v'.first in v'.lsnAUIndex.Values);

    if GetTj(v').freshestRec.Some? {
      assert v'.first == v.lsnAUIndex[lbl.startLsn];
      forall addr | addr in GetTj(v').diskView.entries && addr.au != v'.first 
        ensures AUPagesLinkedTillFirstInOrder(GetTj(v').diskView, addr)
      {
        if addr.au == v.first {
          assert v.first != v'.first;

       } else {
        //   assert AUPagesLinkedTillFirstInOrder(GetTj(v).diskView, addr);
        //   var newlsnAUIndex := lsnAUIndexDiscardUpTo(v.lsnAUIndex, lbl.startLsn);
        //   var discardedAUs := v.lsnAUIndex.Values - newlsnAUIndex.Values;

        //   assert addr.au !in discardedAUs;
        //   // GetTj(v).diskView.BlocksCanFollow 
        //   // Canconcat
          assume false;
        }
      }
      assert InternalAUPagesFullyLinked(GetTj(v').diskView, v'.first);
    }
  }

  lemma InitRefines()
  {

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
      // case ReadForRecoveryStep(depth) => {
      //   assert LinkedJournal.NextStep(I(v), I(v'), lbl.I(), IStep(step));
      // }
      // case FreezeForCommitStep(depth) => {
      //   assert LinkedJournal.NextStep(I(v), I(v'), lbl.I(), IStep(step));
      // } 
      // case ObserveFreshJournalStep() => {
      //   assert LinkedJournal.NextStep(I(v), I(v'), lbl.I(), IStep(step));
      // } 
      // case PutStep() => {
      //   assert LinkedJournal.NextStep(I(v), I(v'), lbl.I(), IStep(step));
      // }
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
      // case InternalNoOpStep() => {
      //   assert LinkedJournal.NextStep(I(v), I(v'), lbl.I(), IStep(step));
      // }
      case _ => {
        assume false;
      }
    }
  }
}