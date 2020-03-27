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

  datatype CommitterModel = CommitterModel(
    journalist: JournalistModel.JournalistModel,
    frozenLoc: Option<Location>,
    isFrozen: bool,

    frozenJournalPosition: uint64,
    superblockWrite: Option<JC.ReqId>,

    outstandingJournalWrites: seq<JC.ReqId>,

    superblock: Superblock,
    newSuperblock: Superblock,
    whichSuperblock: uint64,
    commitStatus: JC.CommitStatus,

    syncReqs: MutableMapModel.LinearHashMap<JC.SyncReqStatus>
  )
}
