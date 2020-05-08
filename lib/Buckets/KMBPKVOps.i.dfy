include "../Base/NativeTypes.s.dfy"
include "../Base/KeyType.s.dfy"
include "../DataStructures/KMBtree.i.dfy"
include "PackedKV.i.dfy"

module KMBPKVOps {
  import opened NativeTypes
  import PKV = PackedKV
  import KMB = KMBtree`All
  import KMBBOps = KMBtreeBulkOperations
  import DPKV = DynamicPkv
  import KeyType
  import ValueType = ValueType`Internal
  import opened Sequences

  function messageSeq_to_bytestringSeq(msgs: seq<KMB.Model.Messages.Message>) : (result: seq<seq<byte>>)
    requires forall i | 0 <= i < |msgs| :: msgs[i].Define?
    ensures |result| == |msgs|
    ensures forall i | 0 <= i < |result| :: result[i] == PKV.Message_to_bytestring(msgs[i])
  {
    if |msgs| == 0 then
      []
    else
      messageSeq_to_bytestringSeq(DropLast(msgs)) + [ PKV.Message_to_bytestring(Last(msgs)) ]
  }

  function bytestringSeq_to_MessageSeq(strings: seq<seq<byte>>) : (result: seq<KMB.Model.Messages.Message>)
    requires forall i | 0 <= i < |strings| :: |strings[i]| < 0x1_0000_0000
    ensures |result| == |strings|
    ensures forall i | 0 <= i < |strings| :: result[i] == PKV.bytestring_to_Message(strings[i])
  {
    if |strings| == 0 then
      []
    else
      bytestringSeq_to_MessageSeq(DropLast(strings)) + [ PKV.bytestring_to_Message(Last(strings)) ]
  }
  
  method MessageArray_to_bytestringSeq(msgs: array<KMB.Model.Messages.Message>, nmsgs: uint64) returns (result: seq<seq<byte>>)
    requires nmsgs as nat <= msgs.Length
    requires forall i | 0 <= i < nmsgs as int :: msgs[i].Define?
    ensures result[..] == messageSeq_to_bytestringSeq(msgs[..nmsgs])
  {
    var aresult := new seq<byte>[nmsgs];
    var i: uint64 := 0;

    while i < nmsgs
      invariant i <= nmsgs
      invariant aresult[..i] == messageSeq_to_bytestringSeq(msgs[..i])
    {
      aresult[i] := PKV.Message_to_bytestring(msgs[i]);
      i := i + 1;
    }

    result := aresult[..i];
  }
  
  method LeafFillDpkv(node: KMB.Node, dpkv: DPKV.DynamicPkv)
    requires KMB.WF(node)
    requires node.contents.Leaf?
    requires dpkv.WF()
    requires node.repr !! dpkv.Repr
    requires forall k | k in KMB.Interpretation(node) :: |k| <= KeyType.MaxLen() as nat
    requires forall v | v in KMB.Interpretation(node).Values :: v.Define?
    requires PKV.PSA.psaCanAppendSeq(dpkv.toPkv().keys, KMB.ToSeq(node).0)
    requires forall i | 0 <= i < |KMB.ToSeq(node).1| :: KMB.ToSeq(node).1[i].Define?
    requires PKV.PSA.psaCanAppendSeq(dpkv.toPkv().messages, messageSeq_to_bytestringSeq(KMB.ToSeq(node).1))
    ensures dpkv.WF()
    ensures fresh(dpkv.Repr - old(dpkv.Repr))
    ensures PKV.IKeys(dpkv.toPkv().keys) == old(PKV.IKeys(dpkv.toPkv().keys)) + KMB.ToSeq(node).0
    ensures PKV.IMessages(dpkv.toPkv().messages) == old(PKV.IMessages(dpkv.toPkv().messages)) + KMB.ToSeq(node).1
    modifies dpkv.Repr
    decreases node.height
  {
    var keys := node.contents.keys;
    var values := node.contents.values;
    var nkeys := node.contents.nkeys;
    
    assert KMB.ToSeq(node).0 == keys[..nkeys] by {
      KMB.reveal_I();
      KMB.Model.reveal_ToSeq();
    }

    assert KMB.ToSeq(node).1 == values[..nkeys] by {
      KMB.reveal_I();
      KMB.Model.reveal_ToSeq();
    }        

    forall i | 0 <= i < nkeys
      ensures keys[i] in KMB.Interpretation(node)
    {
      KMB.reveal_I();
      KMB.Model.reveal_Interpretation();
    }
    
    var messages := MessageArray_to_bytestringSeq(values, nkeys);
    dpkv.keys.AppendSeq(keys[..nkeys]);
    dpkv.messages.AppendSeq(messages);
    dpkv.Repr := {dpkv} + dpkv.keys.Repr + dpkv.messages.Repr;

    calc {
      PKV.IMessages(dpkv.toPkv().messages);
      bytestringSeq_to_MessageSeq(PKV.PSA.I(dpkv.toPkv().messages));
      old(PKV.IMessages(dpkv.toPkv().messages)) + values[..nkeys];
    }
  }

  // } else {
  //   assume false;
  //   while i < node.contents.nchildren
  //     invariant i <= node.contents.nchildren
  //     invariant dpkv.WF()
  //     invariant fresh(dpkv.Repr - old(dpkv.Repr))
  //   {
  //     KMB.IOfChild(node, i as int);
  //     assert KMB.WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height);
  //     FillDpkv(node.contents.children[i], dpkv);
  //     i := i + 1;
  //   }
  // }

  method ToPkv(node: KMB.Node) returns (pkv: DPKV.PKV.Pkv)
    requires KMB.WF(node)
    ensures DPKV.PKV.WF(pkv)
  {
    assume false;
    var nelts: uint64 := KMBBOps.CountElements(node);
    var cap := DPKV.Capacity(nelts as uint32, (nelts * KeyType.MaxLen()) as uint32, (nelts * ValueType.MaxLen()) as uint32);
    var dpkv := new DPKV.DynamicPkv.PreSized(cap);
    //FillDpkv(node, dpkv);
    pkv := dpkv.toPkv();
  }

  // I don't think we use this much (if at all?) so not optimizing for now.
  method FromPkv(pkv: DPKV.PKV.Pkv) returns (node: KMB.Node)
    requires DPKV.PKV.WF(pkv)
    ensures KMB.WF(node)
    ensures fresh(node.repr)
  {
    var i: uint64 := 0;
    var oldvalue;
    
    node := KMB.EmptyTree();
    
    while i < DPKV.PKV.NumKVPairs(pkv)
      invariant i <= DPKV.PKV.NumKVPairs(pkv)
      invariant KMB.WF(node)
      invariant fresh(node.repr)
    {
      node, oldvalue := KMB.Insert(node, DPKV.PKV.GetKey(pkv, i), DPKV.PKV.GetMessage(pkv, i));
      i := i + 1;
    }
  }
  
  
}
