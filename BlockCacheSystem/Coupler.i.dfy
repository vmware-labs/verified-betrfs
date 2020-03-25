module Coupler {

  // HIgh level thing

  datatype VersionedMap = VersionedMap(
    states: seq<MapSpec>,
    persistentIndex: Version,
    syncReqs: map<SyncId, Version>
  )

  datatype VersionedMapStep =
      | Write
      | Crash
      | Sync

  // Journaloo

  datatype Journaloo = Journaloo(
    states: seq<MapSpec>,
    persistentJournalIndex: Version,
    persistentGraphIndex: Version,
    frozenGraphIndex: Option<Version>,
    frozenIndirectionTableLoc: Location,
    persistentIndirectionTableLoc: Location,
    syncReqs: map<SyncId, Version>
  )

  datatype JournalooStep =
    | Write
    | Crash // forget frozen stuff
    | AdvanceJournal // persistentJournalIndex gets bigger
    | NoOp
    | Freeze // frozenIndex := |states|
    | FrozenReadyToWrite // initialize frozenIndirectionTableLoc
    | TruncateDone // update persistentIndirectionTableLoc := frozenIndirectionTableLoc
               // persistentIndex := frozenIndex
               // frozenIndex := None
               // frozenIndirectionTableLoc := None
    | LearnLocation // 

  datatype GraphKeeper = GraphKeeper(
    disk: map<Location, Map> // size 2
    ephemeralState: Map,
    frozenState: Map,
    persistentLoc: Location,
    frozenLoc: Location,

  datatype GraphKeeperStep =
    | Write // Advances ephemeralState
    | Crash // forget in-memory stuff
    | Freeze // set frozenState := ephemeralState
    | NoOp // internal stuff, writing out nodes etc
    | WriteFrozenState // conjure frozenLoc and set disk[frozenLoc] := frozenState
    | FrozenReadyToWrite // enabling condition: frozenLoc exists
    | TruncateDone // update persisnteLoc := frozenLoc, frozenLoc := None


  datatype CoordinatorOp = // like diskOp
      | Write
      | Crash
      | JournalooInternal
      | BlockCacheInternal
      | Freeze
      | FrozenReadyToWrite(loc: Location)
      | SyncDone
}
