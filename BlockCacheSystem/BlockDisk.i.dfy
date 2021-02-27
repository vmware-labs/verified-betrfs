// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "../lib/Base/Maps.i.dfy"
include "../Versions/VOp.i.dfy"
include "DiskLayout.i.dfy"
include "SectorType.i.dfy"

//
// An AsyncSectorDiskModel allows concurrent outstanding I/Os to a disk where each "sector"
// is some higher-level Node datatype. A later refinement step shows how to marshall and align
// these Nodes to the byte-ranges of the (trusted) AsyncDiskModel.
//

module BlockDisk {
  import opened NativeTypes
  import opened Maps
  import opened Options
  import opened DiskLayout
  import opened PivotBetreeGraph
  import opened Sequences
  import opened SectorType

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

  datatype Variables = Variables(
    ghost reqReadIndirectionTables: map<ReqId, Location>,
    ghost reqReadNodes: map<ReqId, Location>,

    ghost reqWriteIndirectionTables: map<ReqId, Location>,
    ghost reqWriteNodes: map<ReqId, Location>,

    // The disk:
    ghost indirectionTables: imap<Location, IndirectionTable>,
    ghost nodes: imap<Location, Node>
  )

  predicate Init(s: Variables)
  {
    && s.reqReadIndirectionTables == map[]
    && s.reqReadNodes == map[]

    && s.reqWriteIndirectionTables == map[]
    && s.reqWriteNodes == map[]
  }

  ///////// RecvRead

  predicate RecvReadIndirectionTable(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqReadIndirectionTableOp?
    && dop.id !in s.reqReadIndirectionTables
    && s' == s.(reqReadIndirectionTables := s.reqReadIndirectionTables[dop.id := dop.loc])
  }

  predicate RecvReadNode(s: Variables, s': Variables, dop: DiskOp)
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

  predicate RecvWriteIndirectionTable(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqWriteIndirectionTableOp?
    && dop.id !in s.reqWriteIndirectionTables
    && DiskMapUpdate(s.indirectionTables, s'.indirectionTables, dop.reqWriteIndirectionTable.loc, dop.reqWriteIndirectionTable.indirectionTable)
    && s' == s.(reqWriteIndirectionTables := s.reqWriteIndirectionTables[dop.id := dop.reqWriteIndirectionTable.loc])
              .(indirectionTables := s'.indirectionTables)
  }

  predicate RecvWriteNode(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqWriteNodeOp?
    && dop.id !in s.reqWriteNodes
    && DiskMapUpdate(s.nodes, s'.nodes, dop.reqWriteNode.loc, dop.reqWriteNode.node)
    && s' == s.(reqWriteNodes := s.reqWriteNodes[dop.id := dop.reqWriteNode.loc])
              .(nodes := s'.nodes)
  }

  ///////// AckRead

  predicate AckReadIndirectionTable(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespReadIndirectionTableOp?
    && dop.id in s.reqReadIndirectionTables
    && var loc := s.reqReadIndirectionTables[dop.id];
    && (dop.indirectionTable.Some? ==>
      dop.indirectionTable == ImapLookupOption(s.indirectionTables, loc))
    && s' == s.(reqReadIndirectionTables := MapRemove1(s.reqReadIndirectionTables, dop.id))
  }

  predicate AckReadNode(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespReadNodeOp?
    && dop.id in s.reqReadNodes
    && var loc := s.reqReadNodes[dop.id];
    && (dop.node.Some? ==>
      dop.node == ImapLookupOption(s.nodes, loc))
    && s' == s.(reqReadNodes := MapRemove1(s.reqReadNodes, dop.id))
  }

  ///////// AckWrite

  predicate AckWriteIndirectionTable(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespWriteIndirectionTableOp?
    && dop.id in s.reqWriteIndirectionTables
    && s' == s.(reqWriteIndirectionTables := MapRemove1(s.reqWriteIndirectionTables, dop.id))
  }

  predicate AckWriteNode(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespWriteNodeOp?
    && dop.id in s.reqWriteNodes
    && s' == s.(reqWriteNodes := MapRemove1(s.reqWriteNodes, dop.id))
  }

  //// Stutter

  predicate Stutter(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.NoDiskOp?
    && s' == s
  }

  predicate Next(s: Variables, s': Variables, dop: DiskOp) {
    && (dop.ReqReadIndirectionTableOp? ==> RecvReadIndirectionTable(s, s', dop))
    && (dop.ReqReadNodeOp? ==> RecvReadNode(s, s', dop))

    && (dop.ReqWriteIndirectionTableOp? ==> RecvWriteIndirectionTable(s, s', dop))
    && (dop.ReqWriteNodeOp? ==> RecvWriteNode(s, s', dop))

    && (dop.RespReadIndirectionTableOp? ==> AckReadIndirectionTable(s, s', dop))
    && (dop.RespReadNodeOp? ==> AckReadNode(s, s', dop))

    && (dop.RespWriteIndirectionTableOp? ==> AckWriteIndirectionTable(s, s', dop))
    && (dop.RespWriteNodeOp? ==> AckWriteNode(s, s', dop))

    && (dop.NoDiskOp? ==> Stutter(s, s', dop))
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

  predicate Crash(s: Variables, s': Variables)
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
  import opened ViewOp

  predicate Init(s: Variables)
  predicate Next(s: Variables, s': Variables, dop: D.DiskOp, vop: VOp)
}
