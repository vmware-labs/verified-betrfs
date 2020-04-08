include "CommitterModel.i.dfy"
include "JournalistImpl.i.dfy"
include "../lib/DataStructures/MutableMapImpl.i.dfy"

// for when you have commitment issues

module CommitterImpl {
  import JournalistModel
  import JC = JournalCache
  import opened SectorType
  import opened DiskLayout
  import opened Options
  import opened NativeTypes
  import MutableMap
  import JournalistImpl
  import CommitterModel

  class Committer {
    var status: CommitterModel.Status;

    var journalist: JournalistImpl.Journalist;
    var frozenLoc: Option<Location>;
    var isFrozen: bool;

    var frozenJournalPosition: uint64;
    var superblockWrite: Option<JC.ReqId>;

    var outstandingJournalWrites: set<JC.ReqId>;

    var superblock: Superblock;
    var newSuperblock: Option<Superblock>;
    var whichSuperblock: uint64;
    var commitStatus: JC.CommitStatus;

    var journalFrontRead: Option<JC.ReqId>;
    var journalBackRead: Option<JC.ReqId>;
    var superblock1Read: Option<JC.ReqId>;
    var superblock2Read: Option<JC.ReqId>;
    var superblock1: JC.SuperblockReadResult;
    var superblock2: JC.SuperblockReadResult;

    var syncReqs: MutableMap.ResizingHashMap<JC.SyncReqStatus>;

    ghost var Repr: set<object>;

    predicate ProtectedReprInv()
    reads this, this.Repr
    {
      && this in Repr
      && this.syncReqs in Repr
      && this.journalist in Repr
      && this.Repr == {this} + this.syncReqs.Repr + this.journalist.Repr
      && this !in this.syncReqs.Repr
      && this !in this.journalist.Repr
      && this.syncReqs.Repr !! this.journalist.Repr
    }

    protected predicate ReprInv()
    reads this, this.Repr
    ensures ReprInv() ==> this in this.Repr
    {
      ProtectedReprInv()
    }

    lemma reveal_ReprInv()
    ensures ReprInv() <==> ProtectedReprInv()
    {
    }

    predicate W()
    reads this, this.Repr
    {
      && ReprInv()
      && this.syncReqs.Inv()
      && this.journalist.Inv()
    }

    function I() : CommitterModel.CM
    reads this, this.Repr
    requires W()
    {
      CommitterModel.CM(
        status,
        journalist.I(),
        frozenLoc,
        isFrozen,
        frozenJournalPosition,
        superblockWrite,
        outstandingJournalWrites,
        superblock,
        newSuperblock,
        whichSuperblock,
        commitStatus,
        journalFrontRead,
        journalBackRead,
        superblock1Read,
        superblock2Read,
        superblock1,
        superblock2,
        syncReqs.I()
      )
    }

    predicate WF()
    reads this, this.Repr
    {
      && W()
      && CommitterModel.WF(I())
    }

    predicate Inv()
    reads this, this.Repr
    {
      && W()
      && CommitterModel.Inv(I())
    }

    constructor()
    ensures Inv()
    ensures fresh(Repr)
    ensures CommitterModel.I(I())
        == JC.LoadingSuperblock(
            None, None,
            JC.SuperblockUnfinished,
            JC.SuperblockUnfinished,
            map[])
    {
      journalist := new JournalistImpl.Journalist();
      syncReqs := new MutableMap.ResizingHashMap(128);
      status := CommitterModel.StatusLoadingSuperblock;
      superblock1Read := None;
      superblock2Read := None;
      superblock1 := JC.SuperblockUnfinished;
      superblock2 := JC.SuperblockUnfinished;

      new;
      Repr := {this} + this.syncReqs.Repr + this.journalist.Repr;
    }
  }
}
