include "../Base/NativeTypes.s.dfy"
include "../Base/KeyType.s.dfy"
include "../DataStructures/KMBtree.i.dfy"
include "PackedKV.i.dfy"
include "BucketsLib.i.dfy"
include "BucketWeights.i.dfy"

module KMBPKVOps {
  import opened NativeTypes
  import PKV = PackedKV
  import KMB = KMBtree`All
  import KMBBOps = KMBtreeBulkOperations
  import DPKV = DynamicPkv
  import KeyType
  import ValueType = ValueType`Internal
  import ValueMessage = ValueMessage`Internal
  import opened Sequences
  import opened Maps
  import BucketsLib
  import BucketWeights
  

  predicate IsKeyMessageTree(node: KMB.Node)
    reads node, node.repr
  {
    && KMB.WF(node)
    && (forall k | k in KMB.Interpretation(node) :: PKV.ValidKeyByteString(k))
    && (forall v | v in KMB.Interpretation(node).Values :: ValueMessage.EncodableMessage(v))
    //&& ValueMessage.EncodableMessageSeq(KMB.ToSeq(node).1)
  }

  lemma KMTreeEncodableToSeq(node: KMB.Node)
    requires IsKeyMessageTree(node)
    ensures ValueMessage.EncodableMessageSeq(KMB.ToSeq(node).1)
  {
    KMB.Model.ToSeqInInterpretation(KMB.I(node));
  }
  
  lemma IsKeyMessageTreeInheritance(node: KMB.Node, i: nat)
    requires KMB.WF(node)
    requires node.contents.Index?
    requires IsKeyMessageTree(node)
    requires i < node.contents.nchildren as nat
    ensures IsKeyMessageTree(node.contents.children[i])
  {
    KMB.IOfChild(node, i);
    var inode := KMB.I(node);
    KMB.Model.ChildInterpretationSubMap(inode, i);
    
    var cs := KMB.Model.ToSeqChildren(inode.children).1;
    calc {
      KMB.ToSeq(node).1;
      KMB.Model.ToSeq(KMB.I(node)).1;
      KMB.Model.ToSeq(inode).1;
      { KMB.Model.reveal_ToSeq(); }
      Flatten(cs);
    }

    var csA := KMB.Model.ToSeqChildren(inode.children[..i]).1;
    var csB := KMB.Model.ToSeqChildren(inode.children[i..i+1]).1;
    var csC := KMB.Model.ToSeqChildren(inode.children[i+1..]).1;
    calc {
      KMB.Model.ToSeqChildren(inode.children).1;
      {
        KMB.Model.ToSeqChildrenAdditive(inode.children[..i], inode.children[i..]);
        assert inode.children == inode.children[..i] + inode.children[i..];
      }
      csA + KMB.Model.ToSeqChildren(inode.children[i..]).1;
      {
        KMB.Model.ToSeqChildrenAdditive(inode.children[i..i+1], inode.children[i+1..]);
        assert inode.children[i..] == inode.children[i..i+1] + inode.children[i+1..];
      }
      csA + csB + csC;
    }

    calc {
      Flatten(cs);
      { FlattenAdditive(csA + csB, csC); }
      Flatten(csA + csB) + Flatten(csC);
      { FlattenAdditive(csA, csB); }
      Flatten(csA) + Flatten(csB) + Flatten(csC);
    }

    assert csB == [ KMB.Model.ToSeq(inode.children[i]).1 ];
    assert Flatten(csB) == KMB.Model.ToSeq(inode.children[i]).1 by {
      FlattenSingleton(KMB.Model.ToSeq(inode.children[i]).1);
    }

    assert forall m | m in KMB.ToSeq(node.contents.children[i]).1 :: m in KMB.ToSeq(node).1;
    forall m | m in KMB.ToSeq(node.contents.children[i]).1
      ensures ValueMessage.EncodableMessage(m)
    {
      KMTreeEncodableToSeq(node);
    }
  }

  method LeafFillDpkv(node: KMB.Node, dpkv: DPKV.DynamicPkv)
    requires KMB.WF(node)
    requires node.contents.Leaf?
    requires dpkv.WF()
    requires node.repr !! dpkv.Repr
    requires IsKeyMessageTree(node)
    requires PKV.PSA.psaCanAppendSeq(dpkv.toPkv().keys, KMB.ToSeq(node).0)
    requires (KMTreeEncodableToSeq(node); PKV.PSA.psaCanAppendSeq(dpkv.toPkv().messages, ValueMessage.messageSeq_to_bytestringSeq(KMB.ToSeq(node).1)))
    ensures dpkv.WF()
    ensures fresh(dpkv.Repr - old(dpkv.Repr))
    ensures dpkv.toPkv().keys == PKV.PSA.psaAppendSeq(old(dpkv.toPkv().keys), KMB.ToSeq(node).0)
    //ensures PKV.IKeys(dpkv.toPkv().keys) == old(PKV.IKeys(dpkv.toPkv().keys)) + KMB.ToSeq(node).0
    ensures dpkv.toPkv().messages == PKV.PSA.psaAppendSeq(old(dpkv.toPkv().messages), ValueMessage.messageSeq_to_bytestringSeq(KMB.ToSeq(node).1))
    //ensures PKV.IMessages(dpkv.toPkv().messages) == old(PKV.IMessages(dpkv.toPkv().messages)) + KMB.ToSeq(node).1
    modifies dpkv.Repr
  {
    KMTreeEncodableToSeq(node); 
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
    
    var messages := ValueMessage.MessageArray_to_bytestringSeq(values, nkeys);
    dpkv.keys.AppendSeq(keys[..nkeys]);
    dpkv.messages.AppendSeq(messages);
    dpkv.Repr := {dpkv} + dpkv.keys.Repr + dpkv.messages.Repr;

  }

  lemma canAppendKeysIterate(pkv: PKV.Pkv, keyseqs: seq<seq<KMB.Model.Key>>)
    requires PKV.WF(pkv)
    requires 0 < |keyseqs|
    requires PKV.PSA.psaCanAppendSeq(pkv.keys, Flatten(keyseqs))
    ensures PKV.PSA.psaCanAppendSeq(pkv.keys, keyseqs[0])
    ensures PKV.PSA.psaCanAppendSeq(PKV.PSA.psaAppendSeq(pkv.keys, keyseqs[0]), Flatten(keyseqs[1..]))
  {
    calc ==> {
      PKV.PSA.psaCanAppendSeq(pkv.keys, Flatten(keyseqs));
      { assert keyseqs == keyseqs[..1] + keyseqs[1..]; }
      PKV.PSA.psaCanAppendSeq(pkv.keys, Flatten(keyseqs[..1] + keyseqs[1..]));
      { FlattenAdditive(keyseqs[..1], keyseqs[1..]); }
      PKV.PSA.psaCanAppendSeq(pkv.keys, Flatten(keyseqs[..1]) + Flatten(keyseqs[1..]));
      { PKV.PSA.psaCanAppendSeqAdditive(pkv.keys, Flatten(keyseqs[..1]), Flatten(keyseqs[1..])); }
      PKV.PSA.psaCanAppendSeq(pkv.keys, Flatten(keyseqs[..1]))
        && PKV.PSA.psaCanAppendSeq(PKV.PSA.psaAppendSeq(pkv.keys, Flatten(keyseqs[..1])), Flatten(keyseqs[1..]));
      {
        reveal_Flatten();
        assert keyseqs[0] == Last(keyseqs[..1]);
        assert |DropLast(keyseqs[..1])| == 0;
        assert [] + keyseqs[0] == keyseqs[0];
      }
      PKV.PSA.psaCanAppendSeq(pkv.keys, keyseqs[0])
        && PKV.PSA.psaCanAppendSeq(PKV.PSA.psaAppendSeq(pkv.keys, keyseqs[0]), Flatten(keyseqs[1..]));
    }
  }
  
  lemma canAppendMessagesIterate(pkv: PKV.Pkv, msgseqs: seq<seq<KMB.Model.Messages.Message>>)
    requires PKV.WF(pkv)
    requires 0 < |msgseqs|
    requires ValueMessage.EncodableMessageSeq(Flatten(msgseqs))
    requires PKV.PSA.psaCanAppendSeq(pkv.messages, ValueMessage.messageSeq_to_bytestringSeq(Flatten(msgseqs)))
    ensures ValueMessage.EncodableMessageSeq(msgseqs[0])
    ensures ValueMessage.EncodableMessageSeq(Flatten(msgseqs[1..]))
    ensures PKV.PSA.psaCanAppendSeq(pkv.messages, ValueMessage.messageSeq_to_bytestringSeq(msgseqs[0]))
    ensures PKV.PSA.psaCanAppendSeq(PKV.PSA.psaAppendSeq(pkv.messages, ValueMessage.messageSeq_to_bytestringSeq(msgseqs[0])), ValueMessage.messageSeq_to_bytestringSeq(Flatten(msgseqs[1..])))
  {
    calc {
      Flatten(msgseqs);
      {
        assert msgseqs == msgseqs[..1] + msgseqs[1..];
        FlattenAdditive(msgseqs[..1], msgseqs[1..]);
      }
      Flatten(msgseqs[..1]) + Flatten(msgseqs[1..]);
      { assert msgseqs[..1] == [ msgseqs[0] ]; }
      Flatten([ msgseqs[0] ]) + Flatten(msgseqs[1..]);
      { FlattenSingleton(msgseqs[0]); }
      msgseqs[0] + Flatten(msgseqs[1..]);
    }
    forall m | m in msgseqs[0]
      ensures ValueMessage.EncodableMessage(m)
    {
      assert m in Flatten(msgseqs);
    }
    forall m | m in Flatten(msgseqs[1..])
      ensures ValueMessage.EncodableMessage(m)
    {
      assert m in Flatten(msgseqs);
    }

    ValueMessage.messageSeq_to_bytestringSeq_Additive(msgseqs[0], Flatten(msgseqs[1..]));
    PKV.PSA.psaCanAppendSeqAdditive(pkv.messages, ValueMessage.messageSeq_to_bytestringSeq(msgseqs[0]), ValueMessage.messageSeq_to_bytestringSeq(Flatten(msgseqs[1..])));
  }
  
  // TODO(robj): Break this method up.
  method IndexFillDpkv(node: KMB.Node, dpkv: DPKV.DynamicPkv)
    requires KMB.WF(node)
    requires node.contents.Index?
    requires dpkv.WF()
    requires node.repr !! dpkv.Repr
    requires IsKeyMessageTree(node)
    requires PKV.PSA.psaCanAppendSeq(dpkv.toPkv().keys, KMB.ToSeq(node).0)
    requires (KMTreeEncodableToSeq(node); PKV.PSA.psaCanAppendSeq(dpkv.toPkv().messages, ValueMessage.messageSeq_to_bytestringSeq(KMB.ToSeq(node).1)))
    ensures dpkv.WF()
    ensures fresh(dpkv.Repr - old(dpkv.Repr))
    ensures dpkv.toPkv().keys == PKV.PSA.psaAppendSeq(old(dpkv.toPkv().keys), KMB.ToSeq(node).0)
    ensures dpkv.toPkv().messages == PKV.PSA.psaAppendSeq(old(dpkv.toPkv().messages), ValueMessage.messageSeq_to_bytestringSeq(KMB.ToSeq(node).1))
    modifies dpkv.Repr
    decreases node.height, 0
  {
    var children := node.contents.children;
    var nchildren := node.contents.nchildren;

    assert KMB.WFShapeChildren(children[..nchildren], node.repr, node.height);
    ghost var inode := KMB.I(node);
    ghost var ichildren := inode.children;
    forall i | 0 <= i < |ichildren|
      ensures ichildren[i] == KMB.IChildren(children[..nchildren], node.height)[i]
    {
      KMB.IOfChild(node, i);
    }
    assert ichildren == KMB.IChildren(children[..nchildren], node.height);
    ghost var childSeqs := KMB.Model.ToSeqChildren(ichildren);
    assert forall i | 0 <= i < |childSeqs.0| :: childSeqs.0[i] == KMB.ToSeq(children[i]).0 by {
      KMB.Model.reveal_ToSeq();
    }
    assert forall i | 0 <= i < |childSeqs.1| :: childSeqs.1[i] == KMB.ToSeq(children[i]).1 by {
      KMB.Model.reveal_ToSeq();
    }

    assert Flatten(childSeqs.0) == KMB.ToSeq(node).0 by {
      KMB.reveal_I();
      KMB.Model.reveal_ToSeq();
    }
    assert Flatten(childSeqs.1) == KMB.ToSeq(node).1 by {
      KMB.reveal_I();
      KMB.Model.reveal_ToSeq();
    }
    KMTreeEncodableToSeq(node);
    assert ValueMessage.EncodableMessageSeq(Flatten(childSeqs.1));
    forall i | 0 <= i <= nchildren
      ensures ValueMessage.EncodableMessageSeq(Flatten(childSeqs.1[..i]))
      ensures ValueMessage.EncodableMessageSeq(Flatten(childSeqs.1[i..]))
    {
      FlattenAdditive(childSeqs.1[..i], childSeqs.1[i..]);
      assert childSeqs.1 == childSeqs.1[..i] + childSeqs.1[i..];
      assert forall m | m in Flatten(childSeqs.1) :: ValueMessage.EncodableMessage(m);
    }

    ghost var oldpkvkeys := old(dpkv.toPkv().keys);
    ghost var oldpkvmsgs := old(dpkv.toPkv().messages);

    forall i | 0 <= i <= nchildren
      ensures PKV.PSA.psaCanAppendSeq(oldpkvkeys, Flatten(childSeqs.0[..i]))
      ensures PKV.PSA.psaCanAppendSeq(oldpkvmsgs, ValueMessage.messageSeq_to_bytestringSeq(Flatten(childSeqs.1[..i])))
    {
      FlattenAdditive(childSeqs.0[..i], childSeqs.0[i..]);
      assert childSeqs.0 == childSeqs.0[..i] + childSeqs.0[i..];
      PKV.PSA.psaCanAppendSeqAdditive(oldpkvkeys, Flatten(childSeqs.0[..i]), Flatten(childSeqs.0[i..]));

      FlattenAdditive(childSeqs.1[..i], childSeqs.1[i..]);
      assert childSeqs.1 == childSeqs.1[..i] + childSeqs.1[i..];
      ValueMessage.messageSeq_to_bytestringSeq_Additive(Flatten(childSeqs.1[..i]), Flatten(childSeqs.1[i..]));
      PKV.PSA.psaCanAppendSeqAdditive(oldpkvmsgs, ValueMessage.messageSeq_to_bytestringSeq(Flatten(childSeqs.1[..i])),
        ValueMessage.messageSeq_to_bytestringSeq(Flatten(childSeqs.1[i..])));
    }
    
    var i: uint64 := 0;

    while i < nchildren
      invariant i <= nchildren
      invariant dpkv.WF()
      invariant fresh(dpkv.Repr - old(dpkv.Repr))
      
      invariant dpkv.toPkv().keys == PKV.PSA.psaAppendSeq(oldpkvkeys, Flatten(childSeqs.0[..i]))
      invariant PKV.PSA.psaCanAppendSeq(dpkv.toPkv().keys, Flatten(childSeqs.0[i..]))

      invariant dpkv.toPkv().messages == PKV.PSA.psaAppendSeq(oldpkvmsgs, ValueMessage.messageSeq_to_bytestringSeq(Flatten(childSeqs.1[..i])))
      invariant PKV.PSA.psaCanAppendSeq(dpkv.toPkv().messages, ValueMessage.messageSeq_to_bytestringSeq(Flatten(childSeqs.1[i..])))
    {
      assert KMB.WF(children[i]);
      assert dpkv.WF();
      assert children[i].repr !! dpkv.Repr;

      IsKeyMessageTreeInheritance(node, i as nat);
      assert IsKeyMessageTree(children[i]);

      canAppendKeysIterate(dpkv.toPkv(), childSeqs.0[i..]);
      canAppendMessagesIterate(dpkv.toPkv(), childSeqs.1[i..]);

      ghost var prekeys := dpkv.toPkv().keys;
      ghost var premsgs := dpkv.toPkv().messages;

      assert PKV.PSA.psaCanAppendSeq(dpkv.toPkv().keys, KMB.ToSeq(children[i]).0);
      FillDpkv(children[i], dpkv);
      
      calc {
        dpkv.toPkv().keys;
        PKV.PSA.psaAppendSeq(prekeys, KMB.ToSeq(children[i]).0);
        PKV.PSA.psaAppendSeq(PKV.PSA.psaAppendSeq(oldpkvkeys, Flatten(childSeqs.0[..i])), KMB.ToSeq(children[i]).0);
        { PKV.PSA.psaAppendSeqAdditive(oldpkvkeys, Flatten(childSeqs.0[..i]), KMB.ToSeq(children[i]).0); }
        PKV.PSA.psaAppendSeq(oldpkvkeys, Flatten(childSeqs.0[..i]) + KMB.ToSeq(children[i]).0);
        PKV.PSA.psaAppendSeq(oldpkvkeys, Flatten(childSeqs.0[..i]) + childSeqs.0[i]);
        { FlattenSingleton(childSeqs.0[i]); }
        PKV.PSA.psaAppendSeq(oldpkvkeys, Flatten(childSeqs.0[..i]) + Flatten([ childSeqs.0[i] ]));
        { FlattenAdditive(childSeqs.0[..i], [ childSeqs.0[i] ]); }
        PKV.PSA.psaAppendSeq(oldpkvkeys, Flatten(childSeqs.0[..i] + [ childSeqs.0[i] ]));
        { assert childSeqs.0[..i+1] == childSeqs.0[..i] + [ childSeqs.0[i] ]; }
        PKV.PSA.psaAppendSeq(oldpkvkeys, Flatten(childSeqs.0[..i+1]));
      }

    
      calc {
        dpkv.toPkv().messages;
        PKV.PSA.psaAppendSeq(premsgs, ValueMessage.messageSeq_to_bytestringSeq(KMB.ToSeq(children[i]).1));
        PKV.PSA.psaAppendSeq(premsgs, ValueMessage.messageSeq_to_bytestringSeq(childSeqs.1[i]));
        PKV.PSA.psaAppendSeq(PKV.PSA.psaAppendSeq(oldpkvmsgs, ValueMessage.messageSeq_to_bytestringSeq(Flatten(childSeqs.1[..i]))),
                                                              ValueMessage.messageSeq_to_bytestringSeq(childSeqs.1[i]));
        { PKV.PSA.psaAppendSeqAdditive(oldpkvmsgs, ValueMessage.messageSeq_to_bytestringSeq(Flatten(childSeqs.1[..i])),
                                                   ValueMessage.messageSeq_to_bytestringSeq(childSeqs.1[i])); }
        PKV.PSA.psaAppendSeq(oldpkvmsgs, ValueMessage.messageSeq_to_bytestringSeq(Flatten(childSeqs.1[..i])) +
                                         ValueMessage.messageSeq_to_bytestringSeq(childSeqs.1[i]));
        { ValueMessage.messageSeq_to_bytestringSeq_Additive(Flatten(childSeqs.1[..i]), childSeqs.1[i]); }
        PKV.PSA.psaAppendSeq(oldpkvmsgs, ValueMessage.messageSeq_to_bytestringSeq(Flatten(childSeqs.1[..i]) + childSeqs.1[i]));
        { FlattenSingleton(childSeqs.1[i]); }
        PKV.PSA.psaAppendSeq(oldpkvmsgs, ValueMessage.messageSeq_to_bytestringSeq(Flatten(childSeqs.1[..i]) + Flatten([ childSeqs.1[i] ])));
        { FlattenAdditive(childSeqs.1[..i], [ childSeqs.1[i] ]); }
        PKV.PSA.psaAppendSeq(oldpkvmsgs, ValueMessage.messageSeq_to_bytestringSeq(Flatten(childSeqs.1[..i] + [ childSeqs.1[i] ])));
        { assert childSeqs.1[..i+1] == childSeqs.1[..i] + [ childSeqs.1[i] ]; }
        PKV.PSA.psaAppendSeq(oldpkvmsgs, ValueMessage.messageSeq_to_bytestringSeq(Flatten(childSeqs.1[..i+1])));
      }
      
      i := i + 1;
    }

    calc {
      dpkv.toPkv().keys;
      PKV.PSA.psaAppendSeq(oldpkvkeys, Flatten(childSeqs.0[..i]));
      { assert childSeqs.0[..i] == childSeqs.0; }
      PKV.PSA.psaAppendSeq(old(dpkv.toPkv().keys), KMB.ToSeq(node).0);
    }
    calc {
      dpkv.toPkv().messages;
      PKV.PSA.psaAppendSeq(oldpkvmsgs, ValueMessage.messageSeq_to_bytestringSeq(Flatten(childSeqs.1[..i])));
      { assert childSeqs.1[..i] == childSeqs.1; }
      PKV.PSA.psaAppendSeq(old(dpkv.toPkv().messages), ValueMessage.messageSeq_to_bytestringSeq(KMB.ToSeq(node).1));
    }
  }

  method FillDpkv(node: KMB.Node, dpkv: DPKV.DynamicPkv)
    requires KMB.WF(node)
    requires dpkv.WF()
    requires node.repr !! dpkv.Repr
    requires IsKeyMessageTree(node)
    requires PKV.PSA.psaCanAppendSeq(dpkv.toPkv().keys, KMB.ToSeq(node).0)
    requires (KMTreeEncodableToSeq(node); PKV.PSA.psaCanAppendSeq(dpkv.toPkv().messages, ValueMessage.messageSeq_to_bytestringSeq(KMB.ToSeq(node).1)))
    ensures dpkv.WF()
    ensures fresh(dpkv.Repr - old(dpkv.Repr))
    ensures dpkv.toPkv().keys == PKV.PSA.psaAppendSeq(old(dpkv.toPkv().keys), KMB.ToSeq(node).0)
    ensures dpkv.toPkv().messages == PKV.PSA.psaAppendSeq(old(dpkv.toPkv().messages), ValueMessage.messageSeq_to_bytestringSeq(KMB.ToSeq(node).1))
    modifies dpkv.Repr
    decreases node.height, 1
  {
    if node.contents.Leaf? {
      LeafFillDpkv(node, dpkv);
    } else {
      IndexFillDpkv(node, dpkv);
    }
  }


  function byteSeqSeqToKeySeq(keys: seq<seq<byte>>) : (result: seq<KeyType.Key>)
    requires forall k | k in keys :: |k| <= KeyType.MaxLen() as nat
    ensures result == keys
  {
    seq(|keys|, i requires 0 <= i < |keys| => keys[i])
  }
  
  lemma ToSeqInterpretation(node: KMB.Node)
    requires KMB.WF(node)
    requires IsKeyMessageTree(node)
    ensures forall k | k in KMB.ToSeq(node).0 :: |k| <= KeyType.MaxLen() as nat
    ensures BucketsLib.BucketMapOfSeq(byteSeqSeqToKeySeq(KMB.ToSeq(node).0), KMB.ToSeq(node).1) == KMB.Interpretation(node)
  {
    KMB.Model.ToSeqCoversInterpretation(KMB.I(node));
    KMB.Model.ToSeqInInterpretation(KMB.I(node));
    assert forall k | k in KMB.ToSeq(node).0 :: k in KMB.Interpretation(node);
    var keys: seq<KMB.Model.Key> := byteSeqSeqToKeySeq(KMB.ToSeq(node).0);
    var msgs := KMB.ToSeq(node).1;
    var interp := KMB.Interpretation(node);
    KMB.Model.ToSeqIsStrictlySorted(KMB.I(node));
    assert KMB.Model.Keys.IsStrictlySorted(keys) by {
      KMB.Model.Keys.reveal_IsStrictlySorted();
    }
    BucketsLib.StrictlySortedIsBucketMapOfSeq(keys, msgs, interp);
  }

  lemma IMessagesInverse(pkv: PKV.Pkv, msgs: seq<KMB.Model.Messages.Message>)
    requires PKV.WF(pkv)
    requires ValueMessage.EncodableMessageSeq(msgs)
    requires PKV.PSA.I(pkv.messages) == ValueMessage.messageSeq_to_bytestringSeq(msgs)
    ensures PKV.IMessages(pkv.messages) == msgs
  {
    
  }
  
  lemma ToPkvPreservesInterpretation(node: KMB.Node, pkv: DPKV.PKV.Pkv)
    requires KMB.WF(node)
    requires IsKeyMessageTree(node)
    requires PKV.PSA.psaCanAppendSeq(PKV.PSA.EmptyPsa(), KMB.ToSeq(node).0)
    requires (KMTreeEncodableToSeq(node); PKV.PSA.psaCanAppendSeq(PKV.PSA.EmptyPsa(), ValueMessage.messageSeq_to_bytestringSeq(KMB.ToSeq(node).1)))
    requires DPKV.PKV.WF(pkv)
    requires PKV.IKeys(pkv.keys) == KMB.ToSeq(node).0
    requires PKV.PSA.I(pkv.messages) == ValueMessage.messageSeq_to_bytestringSeq(KMB.ToSeq(node).1)
    ensures DPKV.PKV.I(pkv) == BucketsLib.B(KMB.Interpretation(node))
  {
    KMTreeEncodableToSeq(node);
    var keys := byteSeqSeqToKeySeq(KMB.ToSeq(node).0);
    var msgs := KMB.ToSeq(node).1;
    calc {
      DPKV.PKV.I(pkv).b;
      BucketsLib.BucketMapOfSeq(PKV.IKeys(pkv.keys), PKV.IMessages(pkv.messages));
      { assert PKV.IKeys(pkv.keys) == keys; }
      BucketsLib.BucketMapOfSeq(keys, PKV.IMessages(pkv.messages));
      { IMessagesInverse(pkv, msgs); }
      BucketsLib.BucketMapOfSeq(keys, msgs);
      { ToSeqInterpretation(node); }
      KMB.Interpretation(node);
      BucketsLib.B(KMB.Interpretation(node)).b;
    }
    KMB.Model.ToSeqIsStrictlySorted(KMB.I(node));
    BucketsLib.WellMarshalledBucketsEq(DPKV.PKV.I(pkv), BucketsLib.B(KMB.Interpretation(node)));
  }

  lemma WeightImpliesCanAppend(node: KMB.Node)
    requires KMB.WF(node)
    requires IsKeyMessageTree(node)
    requires BucketWeights.WeightBucket(BucketsLib.B(KMB.Interpretation(node))) < Uint32UpperBound()
    ensures (KMTreeEncodableToSeq(node); PKV.PSA.psaCanAppendSeq(PKV.PSA.EmptyPsa(), KMB.ToSeq(node).0))
    ensures PKV.PSA.psaCanAppendSeq(PKV.PSA.EmptyPsa(), ValueMessage.messageSeq_to_bytestringSeq(KMB.ToSeq(node).1))
  {
    var inode := KMB.I(node);
    KMB.Model.ToSeqInInterpretation(KMB.I(node));
    var keys := byteSeqSeqToKeySeq(KMB.ToSeq(node).0);
    var msgs := KMB.ToSeq(node).1;
    var interp := KMB.Interpretation(node);
    var bucket := BucketsLib.BucketMapWithSeq(interp, keys, msgs);
    ToSeqInterpretation(node);
    KMB.Model.ToSeqIsStrictlySorted(inode);
    
    BucketWeights.NumElementsLteWeight(BucketsLib.B(interp));
    KMB.Model.InterpretationNumElements(inode);
    KMB.Model.ToSeqLength(inode);

    BucketsLib.WellMarshalledBucketsEq(bucket, BucketsLib.B(interp));

    BucketWeights.WeightKeyListFlatten(keys);
    assert keys == BucketsLib.B(interp).keys;

    BucketWeights.WeightMessageListFlatten(msgs);
    assert msgs == BucketsLib.B(interp).msgs;
  }
  
  method ToPkv(node: KMB.Node) returns (pkv: DPKV.PKV.Pkv)
    requires KMB.WF(node)
    requires IsKeyMessageTree(node)
    requires (KMTreeEncodableToSeq(node); PKV.PSA.psaCanAppendSeq(PKV.PSA.EmptyPsa(), KMB.ToSeq(node).0))
    requires PKV.PSA.psaCanAppendSeq(PKV.PSA.EmptyPsa(), ValueMessage.messageSeq_to_bytestringSeq(KMB.ToSeq(node).1))
    ensures DPKV.PKV.WF(pkv)
    ensures PKV.IKeys(pkv.keys) == KMB.ToSeq(node).0
    ensures PKV.PSA.I(pkv.messages) == ValueMessage.messageSeq_to_bytestringSeq(KMB.ToSeq(node).1)
    ensures DPKV.PKV.I(pkv) == BucketsLib.B(KMB.Interpretation(node))
  {
    KMB.Model.ToSeqLength(KMB.I(node));
    var nelts: uint64 := KMBBOps.CountElements(node);
    var keydatasize := if nelts * KeyType.MaxLen() <= 0xffff_ffff then (nelts * KeyType.MaxLen()) as uint32 else 0xffff_ffff;
    var msgdatasize := if nelts * ValueType.MaxLen() <= 0xffff_ffff then (nelts * ValueType.MaxLen()) as uint32 else 0xffff_ffff;
    var cap := DPKV.Capacity(nelts as uint32, keydatasize, msgdatasize);
    var dpkv := new DPKV.DynamicPkv.PreSized(cap);
    FillDpkv(node, dpkv);
    pkv := dpkv.toPkv();
    ToPkvPreservesInterpretation(node, pkv);
  }

  // I don't think we use this much (if at all?) so not optimizing for now.
  method FromPkv(pkv: DPKV.PKV.Pkv) returns (node: KMB.Node, weight: uint64)
    requires DPKV.PKV.WF(pkv)
    ensures KMB.WF(node)
    ensures IsKeyMessageTree(node)
    ensures PKV.I(pkv).b == BucketsLib.B(KMB.Interpretation(node)).b
    ensures weight as nat == BucketWeights.WeightBucket(BucketsLib.B(KMB.Interpretation(node)))
    ensures fresh(node.repr)
  {
    ghost var keys := PKV.IKeys(pkv.keys);
    ghost var msgs := PKV.IMessages(pkv.messages);
    
    var i: uint64 := 0;
    var oldvalue;
    
    node := KMB.EmptyTree();
    weight := 0;
    
    while i < DPKV.PKV.NumKVPairs(pkv)
      invariant i <= DPKV.PKV.NumKVPairs(pkv)
      invariant KMB.WF(node)
      invariant IsKeyMessageTree(node)
      invariant KMB.Interpretation(node) == BucketsLib.BucketMapOfSeq(keys[..i], msgs[..i])
      invariant weight as nat == BucketWeights.WeightBucket(BucketsLib.B(KMB.Interpretation(node)))
      invariant fresh(node.repr)
    {
      calc <= {
        weight as nat;
        BucketWeights.WeightBucket(BucketsLib.B(KMB.Interpretation(node)));
        BucketWeights.WeightBucket(BucketsLib.B(BucketsLib.BucketMapOfSeq(keys[..i], msgs[..i])));
        {
          BucketWeights.WeightWellMarshalledLe(
            BucketsLib.BucketMapWithSeq(BucketsLib.BucketMapOfSeq(keys[..i], msgs[..i]), keys[..i], msgs[..i]),
            BucketsLib.B(BucketsLib.BucketMapOfSeq(keys[..i], msgs[..i])));
        }
        BucketWeights.WeightBucket(BucketsLib.BucketMapWithSeq(BucketsLib.BucketMapOfSeq(keys[..i],
          msgs[..i]), keys[..i], msgs[..i]));
        {
          assert keys == keys[..i] + keys[i..];
          assert msgs == msgs[..i] + msgs[i..];
          BucketWeights.WeightKeyListAdditive(keys[..i], keys[i..]);
          BucketWeights.WeightMessageListAdditive(msgs[..i], msgs[i..]);
        }
        BucketWeights.WeightBucket(BucketsLib.BucketMapWithSeq(BucketsLib.BucketMapOfSeq(keys, msgs),
          keys, msgs));
        BucketWeights.WeightBucket(PKV.I(pkv));
        {
          DPKV.WeightBucketPkv_eq_WeightPkv(pkv);
        }
        PKV.WeightPkv(pkv) as nat;
        0x10_0000_0000;
      }
      ghost var oldinterp := KMB.Interpretation(node);
      ghost var oldweight := weight as nat;
      
      var key := DPKV.PKV.GetKey(pkv, i);
      var msg := DPKV.PKV.GetMessage(pkv, i);
      node, oldvalue := KMB.Insert(node, key, msg);

      weight := weight + BucketWeights.WeightMessageUint64(msg);
      if oldvalue.Some? {
        calc <= {
          BucketWeights.WeightMessageUint64(oldvalue.value) as nat;
          { BucketWeights.WeightBucketSingleton(key, oldvalue.value); }
          BucketWeights.WeightBucket(BucketsLib.SingletonBucket(key, oldvalue.value));
          {
            BucketWeights.WeightWellMarshalledSubsetLe(BucketsLib.SingletonBucket(key, oldvalue.value),
              BucketsLib.B(oldinterp));
          }
          BucketWeights.WeightBucket(BucketsLib.B(oldinterp));
          oldweight;
          weight as nat;
        }
        weight := weight - BucketWeights.WeightMessageUint64(oldvalue.value);

        ghost var map0 := Maps.MapRemove1(oldinterp, key);
        BucketWeights.WeightBucketInduct(BucketsLib.B(map0), key, oldvalue.value);
        BucketWeights.WeightBucketInduct(BucketsLib.B(map0), key, msg);
        assert oldinterp == map0[key := oldvalue.value];
        assert KMB.Interpretation(node) == map0[key := msg];
      } else {
        weight := weight + BucketWeights.WeightKeyUint64(key);
        BucketWeights.WeightBucketInduct(BucketsLib.B(oldinterp), key, msg);
      }

      BucketsLib.reveal_BucketMapOfSeq();
      assert keys[..i+1] == keys[..i] + [ keys[i] ];
      assert msgs[..i+1] == msgs[..i] + [ msgs[i] ];

      i := i + 1;
    }

    assert keys[..i] == keys;
    assert msgs[..i] == msgs;
  }
  
  
}
