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

  function MessageSeq_to_bytestringSeq(msgs: seq<KMB.Model.Messages.Message>) : (result: seq<seq<byte>>)
    requires forall i | 0 <= i < |msgs| :: msgs[i].Define?
    ensures |result| == |msgs|
    ensures forall i | 0 <= i < |result| :: result[i] == PKV.Message_to_bytestring(msgs[i])
  {
    if |msgs| == 0 then
      []
    else
      MessageSeq_to_bytestringSeq(DropLast(msgs)) + [ PKV.Message_to_bytestring(Last(msgs)) ]
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
    requires PKV.PSA.psaCanAppendSeq(dpkv.toPkv().messages, MessageSeq_to_bytestringSeq(KMB.ToSeq(node).1))
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

    ghost var oldpkvkeys := old(PKV.IKeys(dpkv.toPkv().keys));
    ghost var oldpkvmsgs := old(PKV.IMessages(dpkv.toPkv().messages));
    ghost var messages := MessageSeq_to_bytestringSeq(values[..nkeys]);
    
    var i: uint64 := 0;

    assert messages[i..nkeys] == MessageSeq_to_bytestringSeq(KMB.ToSeq(node).1);

    while i < nkeys
      invariant i <= nkeys
      invariant dpkv.WF()
      invariant fresh(dpkv.Repr - old(dpkv.Repr))
      invariant PKV.IKeys(dpkv.toPkv().keys) ==  oldpkvkeys + keys[..i]
      invariant PKV.PSA.psaCanAppendSeq(dpkv.toPkv().keys, keys[i..nkeys])
      invariant PKV.IMessages(dpkv.toPkv().messages) == oldpkvmsgs + values[..i]
      invariant PKV.PSA.psaCanAppendSeq(dpkv.toPkv().messages, messages[i..nkeys])
    {
      assert keys[i] in KMB.Interpretation(node) by {
        KMB.reveal_I();
        KMB.Model.reveal_Interpretation();
      }
      assert keys[i..nkeys] == [ keys[i] ] + keys[i+1..nkeys];
      PKV.PSA.psaCanAppendSeqAdditive(dpkv.toPkv().keys, [ keys[i] ], keys[i+1..nkeys]);
      PKV.PSA.psaCanAppendOne(dpkv.toPkv().keys, keys[i]);

      assert messages[i..nkeys] == [ messages[i] ] + messages[i+1..nkeys];
      PKV.PSA.psaCanAppendSeqAdditive(dpkv.toPkv().messages, [ messages[i] ], messages[i+1..nkeys]);
      PKV.PSA.psaCanAppendOne(dpkv.toPkv().messages, messages[i]);
      
      dpkv.Append(keys[i], node.contents.values[i]);
      
      assert keys[..i+1] == keys[..i] + [ keys[i] ];
      assert messages[..i+1] == messages[..i] + [ messages[i] ];
      assert values[..i+1] == values[..i] + [ values[i] ];
      i := i + 1;
    }
    assert KMB.Model.ToSeq(KMB.I(node)).0 == keys[..i] by {
      KMB.reveal_I();
      KMB.Model.reveal_ToSeq();
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
