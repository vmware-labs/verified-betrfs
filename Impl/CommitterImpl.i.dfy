include "CommitterModel.i.dfy"
include "JournalistImpl.i.dfy"
include "../lib/DataStructures/LinearMutableMap.i.dfy"

// for when you have commitment issues

module CommitterImpl {
  import JournalistModel
  import JC = JournalCache
  import opened SectorType
  import opened DiskLayout
  import opened Options
  import opened NativeTypes
  import LinearMutableMap
  import JournalistImpl
  import CommitterModel

linear datatype Committer = Committer(
    status: CommitterModel.Status,
    linear journalist: JournalistImpl.Journalist,
    frozenLoc: Option<Location>,
    isFrozen: bool,
    frozenJournalPosition: uint64,
    superblockWrite: Option<JC.ReqId>,
    outstandingJournalWrites: set<JC.ReqId>,
    superblock: Superblock,
    newSuperblock: Option<Superblock>,
    whichSuperblock: uint64,
    commitStatus: JC.CommitStatus,
    journalFrontRead: Option<JC.ReqId>,
    journalBackRead: Option<JC.ReqId>,
    superblock1Read: Option<JC.ReqId>,
    superblock2Read: Option<JC.ReqId>,
    superblock1: JC.SuperblockReadResult,
    superblock2: JC.SuperblockReadResult,
    linear syncReqs: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
{
    predicate W()
    {
      && this.syncReqs.Inv()
      && this.journalist.Inv()
    }

    function I() : CommitterModel.CM
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
        syncReqs
      )
    }

    predicate WF()
    {
      && W()
      && CommitterModel.WF(I())
    }

    predicate Inv()
    {
      && W()
      && CommitterModel.Inv(I())
    }

    static method Constructor() returns (linear cm: Committer)
    ensures cm.Inv()
    ensures CommitterModel.I(cm.I())
        == JC.LoadingSuperblock(
            None, None,
            JC.SuperblockUnfinished,
            JC.SuperblockUnfinished,
            map[])
    {
      linear var j := JournalistImpl.Journalist.Constructor();
      linear var m := LinearMutableMap.Constructor(128);
      cm := Committer(
        CommitterModel.StatusLoadingSuperblock,
        j,
        None,
        false,
        0,
        None,
        {},
        Superblock(0, 0, 0, Location(0, 0)),
        None,
        0,
        JC.CommitStatus.CommitNone,
        None,
        None,
        None,
        None,
        JC.SuperblockUnfinished,
        JC.SuperblockUnfinished,
        m
      );
      assert CommitterModel.I(cm.I()) == JC.LoadingSuperblock(
            None, None,
            JC.SuperblockUnfinished,
            JC.SuperblockUnfinished,
            map[]);
    }
  }
}
