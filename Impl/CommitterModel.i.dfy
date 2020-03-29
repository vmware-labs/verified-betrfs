include "../BlockCacheSystem/JournalCache.i.dfy"
include "JournalistModel.i.dfy"
include "../lib/DataStructures/MutableMapModel.i.dfy"

// for when you have commitment issues

module CommitterModel {
  import JournalistModel
  import MutableMapModel
  import JC = JournalCache
  import opened SectorType
  import opened DiskLayout
  import opened Options
  import opened NativeTypes

  datatype Status =
    | StatusLoadingSuperblock
    | StatusLoadingOther
    | StatusReady

  datatype CM = CM(
    status: Status,

    journalist: JournalistModel.JournalistModel,
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

    syncReqs: MutableMapModel.LinearHashMap<JC.SyncReqStatus>
  )

  predicate WF(cm: CM)
  {
    && MutableMapModel.Inv(cm.syncReqs)
    && JournalistModel.Inv(cm.journalist)
    && (cm.status == StatusLoadingSuperblock ==>
      && JournalistModel.I(cm.journalist).inMemoryJournalFrozen == []
      && JournalistModel.I(cm.journalist).inMemoryJournal == []
      && JournalistModel.I(cm.journalist).replayJournal == []
      && JournalistModel.I(cm.journalist).journalFront == None
      && JournalistModel.I(cm.journalist).journalBack == None
      && (cm.superblock1.SuperblockSuccess? ==>
          JC.WFSuperblock(cm.superblock1.value))
      && (cm.superblock2.SuperblockSuccess? ==>
          JC.WFSuperblock(cm.superblock2.value))
    )
    && (cm.status == StatusLoadingOther ==>
      && JournalistModel.I(cm.journalist).inMemoryJournalFrozen == []
      && JournalistModel.I(cm.journalist).inMemoryJournal == []
      && JournalistModel.I(cm.journalist).replayJournal == []
      && JC.WFSuperblock(cm.superblock)
    )
    && (cm.status == StatusReady ==>
      && JC.WFSuperblock(cm.superblock)
    )
  }

  function I(cm: CM) : JC.Variables
  requires WF(cm)
  {
    match cm.status {
      case StatusLoadingSuperblock =>
        JC.LoadingSuperblock(
          cm.superblock1Read,
          cm.superblock2Read,
          cm.superblock1,
          cm.superblock2,
          cm.syncReqs.contents
        )
      case StatusLoadingOther =>
        JC.LoadingOther(
          cm.superblock,
          cm.whichSuperblock as int,
          cm.journalFrontRead,
          cm.journalBackRead,
          JournalistModel.I(cm.journalist).journalFront,
          JournalistModel.I(cm.journalist).journalBack,
          cm.syncReqs.contents
        )
      case StatusReady =>
        JC.Ready(
          cm.frozenLoc,
          cm.isFrozen,
          cm.frozenJournalPosition as int,
          cm.superblockWrite,
          JournalistModel.I(cm.journalist).inMemoryJournalFrozen,
          JournalistModel.I(cm.journalist).inMemoryJournal,
          cm.outstandingJournalWrites,
          JournalistModel.I(cm.journalist).writtenJournalLen,
          JournalistModel.I(cm.journalist).replayJournal,
          cm.superblock,
          cm.whichSuperblock as int,
          cm.commitStatus,
          cm.newSuperblock,
          cm.syncReqs.contents
        )
    }
  }

  predicate Inv(cm: CM)
  {
    && WF(cm)
    && JC.Inv(JC.Constants(), I(cm))
  }
}
