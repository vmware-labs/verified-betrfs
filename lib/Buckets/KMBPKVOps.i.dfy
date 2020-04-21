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

  method FillDpkv(node: KMB.Node, dpkv: DPKV.DynamicPkv)
    requires KMB.WF(node)
    requires dpkv.WF()
    requires node.repr !! dpkv.Repr
    ensures dpkv.WF()
    ensures fresh(dpkv.Repr - old(dpkv.Repr))
    modifies dpkv.Repr
    decreases node.height
  {
    var i: uint64 := 0;

    if node.contents.Leaf? {
      while i < node.contents.nkeys
        invariant i <= node.contents.nkeys
        invariant dpkv.WF()
        invariant fresh(dpkv.Repr - old(dpkv.Repr))
      {
        assume false;
        dpkv.Append(node.contents.keys[i], node.contents.values[i]);
        i := i + 1;
      }
    } else {
      while i < node.contents.nchildren
        invariant i <= node.contents.nchildren
        invariant dpkv.WF()
        invariant fresh(dpkv.Repr - old(dpkv.Repr))
      {
        KMB.IOfChild(node, i as int);
        assert KMB.WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height);
        FillDpkv(node.contents.children[i], dpkv);
        i := i + 1;
      }
    }
  }

  method ToPkv(node: KMB.Node) returns (pkv: DPKV.PKV.Pkv)
    requires KMB.WF(node)
    ensures DPKV.PKV.WF(pkv)
  {
    assume false;
    var nelts: uint64 := KMBBOps.CountElements(node);
    var cap := DPKV.Capacity(nelts as uint32, (nelts * KeyType.MaxLen()) as uint32, (nelts * ValueType.MaxLen()) as uint32);
    var dpkv := new DPKV.DynamicPkv.PreSized(cap);
    FillDpkv(node, dpkv);
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
