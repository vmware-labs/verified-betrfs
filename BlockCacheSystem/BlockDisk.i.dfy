include "../MapSpec/MapSpec.s.dfy"
include "../lib/Base/Maps.s.dfy"
include "../PivotBetree/Bounds.i.dfy"
include "../Versions/VOp.i.dfy"
include "DiskLayout.i.dfy"
include "SectorType.i.dfy"
include "AsyncSectorDiskModelTypes.i.dfy"

//
// An AsyncSectorDiskModel allows concurrent outstanding I/Os to a disk where each "sector"
// is some higher-level Node datatype. A later refinement step shows how to marshall and align
// these Nodes to the byte-ranges of the (trusted) AsyncDiskModel.
//
// TODO disallow concurrent spatially-overlapping writes/reads

// A disk, processing stuff in its queue, doing its thing.
module BlockDisk {
  import opened NativeTypes
  import opened Maps
  import opened Options
  import opened DiskLayout
  import opened SectorType
  import opened PivotBetreeGraph
  import opened Sequences

  type ReqId = uint64

  datatype ReqWriteIndirectionTable = ReqWriteIndirectionTable(loc: Location, indirectionTable: IndirectionTable)
  datatype ReqWriteNode = ReqWriteNode(loc: Location, node: Node)

  datatype DiskOp =
    | ReqReadIndirectionTableOp(id: ReqId, loc: Location)
    | ReqReadNodeOp(id: ReqId, loc: Location)

    | ReqWriteIndirectionTableOp(id: ReqId, reqWriteIndirectionTable: ReqWriteIndirectionTable)
    | ReqWriteNodeOp(id: ReqId, reqWriteNode: ReqWriteNode)

    | RespReadIndirectionTableOp(id: ReqId, indirectionTable: Option<IndirectionTable>)
    | RespReadNodeOp(id: ReqId, node: Option<Node>)

    | RespWriteIndirectionTableOp(id: ReqId)
    | RespWriteNodeOp(id: ReqId)

    | NoDiskOp

  datatype Constants = Constants()
  datatype Variables = Variables(
    ghost reqReadIndirectionTables: map<ReqId, Location>,
    ghost reqReadNodes: map<ReqId, Location>,

    ghost reqWriteIndirectionTables: map<ReqId, Location>,
    ghost reqWriteNodes: map<ReqId, Location>,

    // The disk:
    ghost indirectionTables: imap<Location, IndirectionTable>,
    ghost nodes: imap<Location, Node>
  )

  predicate Init(k: Constants, s: Variables)
  {
    && s.reqReadIndirectionTables == map[]
    && s.reqReadNodes == map[]

    && s.reqWriteIndirectionTables == map[]
    && s.reqWriteNodes == map[]
  }

  ///////// RecvRead

  predicate RecvReadIndirectionTable(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqReadIndirectionTableOp?
    && dop.id !in s.reqReadIndirectionTables
    && s' == s.(reqReadIndirectionTables := s.reqReadIndirectionTables[dop.id := dop.loc])
  }

  predicate RecvReadNode(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqReadNodeOp?
    && dop.id !in s.reqReadNodes
    && s' == s.(reqReadNodes := s.reqReadNodes[dop.id := dop.loc])
  }

  ///////// RecvWrite

  predicate DiskMapUpdate<T>(disk: imap<Location, T>, disk': imap<Location, T>, updateLoc: Location, t: T)
  {
    && updateLoc in disk'
    && disk'[updateLoc] == t
    && (forall loc | loc in disk && !overlap(loc, updateLoc) :: loc in disk' && disk'[loc] == disk[loc])
  }

  predicate RecvWriteIndirectionTable(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqWriteIndirectionTableOp?
    && dop.id !in s.reqWriteIndirectionTables
    && DiskMapUpdate(s.indirectionTables, s'.indirectionTables, dop.reqWriteIndirectionTable.loc, dop.reqWriteIndirectionTable.indirectionTable)
    && s' == s.(reqWriteIndirectionTables := s.reqWriteIndirectionTables[dop.id := dop.reqWriteIndirectionTable.loc])
              .(indirectionTables := s'.indirectionTables)
  }

  predicate RecvWriteNode(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqWriteNodeOp?
    && dop.id !in s.reqWriteNodes
    && DiskMapUpdate(s.nodes, s'.nodes, dop.reqWriteNode.loc, dop.reqWriteNode.node)
    && s' == s.(reqWriteNodes := s.reqWriteNodes[dop.id := dop.reqWriteNode.loc])
              .(nodes := s'.nodes)
  }

  ///////// AckRead

  predicate AckReadIndirectionTable(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespReadIndirectionTableOp?
    && dop.id in s.reqReadIndirectionTables
    && var loc := s.reqReadIndirectionTables[dop.id];
    && (dop.indirectionTable.Some? ==>
      dop.indirectionTable == ImapLookupOption(s.indirectionTables, loc))
    && s' == s.(reqReadIndirectionTables := MapRemove1(s.reqReadIndirectionTables, dop.id))
  }

  predicate AckReadNode(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespReadNodeOp?
    && dop.id in s.reqReadNodes
    && var loc := s.reqReadNodes[dop.id];
    && (dop.node.Some? ==>
      dop.node == ImapLookupOption(s.nodes, loc))
    && s' == s.(reqReadNodes := MapRemove1(s.reqReadNodes, dop.id))
  }

  ///////// AckWrite

  predicate AckWriteIndirectionTable(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespWriteIndirectionTableOp?
    && dop.id in s.reqWriteIndirectionTables
    && s' == s.(reqWriteIndirectionTables := MapRemove1(s.reqWriteIndirectionTables, dop.id))
  }

  predicate AckWriteNode(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespWriteNodeOp?
    && dop.id in s.reqWriteNodes
    && s' == s.(reqWriteNodes := MapRemove1(s.reqWriteNodes, dop.id))
  }

  //// Stutter

  predicate Stutter(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.NoDiskOp?
    && s' == s
  }

  predicate Next(k: Constants, s: Variables, s': Variables, dop: DiskOp) {
    && (dop.ReqReadIndirectionTableOp? ==> RecvReadIndirectionTable(k, s, s', dop))
    && (dop.ReqReadNodeOp? ==> RecvReadNode(k, s, s', dop))

    && (dop.ReqWriteIndirectionTableOp? ==> RecvWriteIndirectionTable(k, s, s', dop))
    && (dop.ReqWriteNodeOp? ==> RecvWriteNode(k, s, s', dop))

    && (dop.RespReadIndirectionTableOp? ==> AckReadIndirectionTable(k, s, s', dop))
    && (dop.RespReadNodeOp? ==> AckReadNode(k, s, s', dop))

    && (dop.RespWriteIndirectionTableOp? ==> AckWriteIndirectionTable(k, s, s', dop))
    && (dop.RespWriteNodeOp? ==> AckWriteNode(k, s, s', dop))

    && (dop.NoDiskOp? ==> Stutter(k, s, s', dop))
  }

  predicate UntouchedLoc(loc: Location, reqs: map<ReqId, Location>)
  {
    forall id | id in reqs :: !overlap(loc, reqs[id])
  }

  predicate havocMap<T>(
    m: imap<Location, T>,
    m': imap<Location, T>,
    reqs: map<ReqId, Location>)
  {
    forall loc | loc in m ::
        UntouchedLoc(loc, reqs) ==>
            loc in m' && m'[loc] == m[loc]
  }

  predicate Crash(k: Constants, s: Variables, s': Variables)
  {
    && s'.reqReadIndirectionTables == map[]
    && s'.reqReadNodes == map[]

    && s'.reqWriteIndirectionTables == map[]
    && s'.reqWriteNodes == map[]

    && havocMap(s.indirectionTables, s'.indirectionTables, s.reqWriteIndirectionTables)
    && havocMap(s.nodes, s'.nodes, s.reqWriteNodes)
  }
}

abstract module BlockMachine {
  import D = BlockDisk
  import UI

  type Variables
  type Constants
  import opened ViewOp

  predicate Init(k: Constants, s: Variables)
  predicate Next(k: Constants, s: Variables, s': Variables, dop: D.DiskOp, vop: VOp)
}

// A disk attached to a program ("Machine"), modeling the nondeterministic crashes that reset the
// program. Designed to look like the AsyncDiskModel, which we want to show refines to this.
// TODO(jonh): Rename this to a "System"?
abstract module BlockSystemModel {
  import D = BlockDisk
  import M : BlockMachine
  import AsyncSectorDiskModelTypes
  import opened SectorType
  import opened ViewOp
  import opened DiskLayout

  type Constants = AsyncSectorDiskModelTypes.AsyncSectorDiskModelConstants<M.Constants, D.Constants>
  type Variables = AsyncSectorDiskModelTypes.AsyncSectorDiskModelVariables<M.Variables, D.Variables>

  datatype Step =
    | MachineStep(dop: D.DiskOp)
    | CrashStep
  
  predicate Machine(k: Constants, s: Variables, s': Variables, dop: D.DiskOp, vop: VOp)
  {
    && M.Next(k.machine, s.machine, s'.machine, dop, vop)
    && D.Next(k.disk, s.disk, s'.disk, dop)
  }

  predicate Crash(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.CrashOp?
    && M.Init(k.machine, s'.machine)
    && D.Crash(k.disk, s.disk, s'.disk)
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, vop: VOp, step: Step)
  {
    match step {
      case MachineStep(dop) => Machine(k, s, s', dop, vop)
      case CrashStep => Crash(k, s, s', vop)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, vop: VOp) {
    exists step :: NextStep(k, s, s', vop, step)
  }

  predicate Init(k: Constants, s: Variables, loc: Location)
  predicate Inv(k: Constants, s: Variables)

  lemma InitImpliesInv(k: Constants, s: Variables, loc: Location)
    requires Init(k, s, loc)
    ensures Inv(k, s)

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp)
    requires Inv(k, s)
    requires Next(k, s, s', vop)
    ensures Inv(k, s')
}
