// include "../lib/Marshalling/GenericMarshalling.i.dfy"
// include "PivotBetreeSpec.i.dfy"
// include "Message.i.dfy"
// include "ImplState.i.dfy"
// include "ImplModel.i.dfy"
// include "KMTable.i.dfy"
// include "../lib/Crypto.s.dfy"
// include "../lib/Option.s.dfy"
// include "../lib/MutableMap.i.dfy"

include "ImplMarshallingModel.i.dfy"

module Marshalling {
  import IMM = ImplMarshallingModel
  import IM = ImplModel
  import opened GenericMarshalling
  import opened Options
  import opened NativeTypes
  import opened Sequences
  // import opened Maps
  import opened BucketsLib
  import BC = BetreeGraphBlockCache
  // import ImplState
  // import IM = ImplModel
  import KMTable
  // import Crypto
  // import Native

  import BT = PivotBetreeSpec`Internal

  import M = ValueMessage`Internal
  // import ReferenceType`Internal
  // import LBAType
  // import ValueWithDefault`Internal

  import Pivots = PivotsLib
  // import MS = MapSpec
  // import Keyspace = MS.Keyspace

  // import MM = MutableMap

  type Reference = BC.Reference
  type LBA = BC.LBA
  type Location = BC.Location
  type Sector = BC.Sector
  type Message = M.Message
  type Key = BT.G.Key
  type Node = BT.G.Node

  /////// Conversion to PivotNode

  function valToIndirectionTable(v: V) : (s : Option<BC.IndirectionTable>)
  requires ValInGrammar(v, IMM.IndirectionTableGrammar())
  ensures s.Some? ==> BC.WFCompleteIndirectionTable(s.value)
  {
    MapOption(IMM.valToIndirectionTable(v), IM.IIndirectionTable)
  }

  function {:fuel ValInGrammar,2} valToBucket(v: V, pivotTable: seq<Key>, i: int) : (s : Option<map<Key, Message>>)
  requires ValidVal(v)
  requires ValInGrammar(v, IMM.BucketGrammar())
  requires Pivots.WFPivots(pivotTable)
  requires 0 <= i <= |pivotTable|
  {
    MapOption(IMM.valToBucket(v, pivotTable, i), KMTable.I)
  }

  function valToBuckets(a: seq<V>, pivotTable: seq<Key>) : (s : Option<seq<map<Key, Message>>>)
  requires Pivots.WFPivots(pivotTable)
  requires forall i | 0 <= i < |a| :: ValidVal(a[i])
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], IMM.BucketGrammar())
  requires |a| <= |pivotTable| + 1
  ensures s.Some? ==> |s.value| == |a|
  ensures s.Some? ==> forall i | 0 <= i < |s.value| :: WFBucketAt(s.value[i], pivotTable, i)
  {
    MapOption(IMM.valToBuckets(a, pivotTable), bkts => Apply(KMTable.I, bkts))
  }


  function {:fuel ValInGrammar,2} valToNode(v: V) : (s : Option<Node>)
  requires ValidVal(v)
  requires ValInGrammar(v, IMM.PivotNodeGrammar())
  ensures s.Some? ==> BT.WFNode(s.value)
  {
    MapOption(IMM.valToNode(v), IM.INode)
  }

  function valToSector(v: V) : (s : Option<BC.Sector>)
  requires ValidVal(v)
  requires ValInGrammar(v, IMM.SectorGrammar())
  {
    MapOption(IMM.valToSector(v), IM.ISector)
  }


  /////// Marshalling and de-marshalling

  function {:opaque} parseSector(data: seq<byte>) : (s : Option<BC.Sector>)
  {
    MapOption(IMM.parseSector(data), IM.ISector)
  }

  /////// Marshalling and de-marshalling with checksums

  function {:opaque} parseCheckedSector(data: seq<byte>) : (s : Option<BC.Sector>)
  {
    MapOption(IMM.parseCheckedSector(data), IM.ISector)
  }
}
