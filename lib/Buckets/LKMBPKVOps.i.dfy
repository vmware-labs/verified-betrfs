include "../Lang/NativeTypes.s.dfy"
include "../Base/KeyType.s.dfy"
include "../DataStructures/KMBtree.i.dfy"
include "PackedKV.i.dfy"
include "BucketsLib.i.dfy"
include "BucketWeights.i.dfy"

module LKMBPKVOps {
  import opened LinearSequence_s
  import opened LinearSequence_i
  import opened NativeTypes
  import PKV = PackedKV
  import LKMB = LKMBtree`All
  import DPKV = DynamicPkv
  import KeyType
  import ValueType = ValueType`Internal
  import ValueMessage = ValueMessage`Internal
  import opened Sequences
  import opened Maps
  import BucketsLib
  import BucketWeights
  import MapSeqs

  predicate IsKeyMessageTree(node: LKMB.Model.Node)
  {
    && LKMB.WF(node)
    && (forall k | k in LKMB.Interpretation(node) :: PKV.ValidKeyByteString(k))
    && (forall v | v in LKMB.Interpretation(node).Values :: ValueMessage.EncodableMessage(v))
  }

  lemma LKMTreeEncodableToSeq(node: LKMB.Model.Node)
    requires IsKeyMessageTree(node)
    ensures ValueMessage.EncodableMessageSeq(LKMB.Model.ToSeq(node).1)
  {
    LKMB.Model.ToSeqInInterpretation(node);
  }

  lemma IsKeyMessageTreeInheritance(node: LKMB.Model.Node, i: nat)
    requires LKMB.WF(node)
    requires node.Index?
    requires IsKeyMessageTree(node)
    requires i < |node.children|
    ensures IsKeyMessageTree(node.children[i])
  {
    var inode := node;
    var children := lseqs(inode.children);
    LKMB.Model.ChildInterpretationSubMap(inode, i);
    
    var cs := LKMB.Model.ToSeqChildren(children).1;
    calc {
      LKMB.Model.ToSeq(node).1;
      LKMB.Model.ToSeq(inode).1;
      { LKMB.Model.reveal_ToSeq(); }
      Flatten(cs);
    }

    var csA := LKMB.Model.ToSeqChildren(children[..i]).1;
    var csB := LKMB.Model.ToSeqChildren(children[i..i+1]).1;
    var csC := LKMB.Model.ToSeqChildren(children[i+1..]).1;
    calc {
      LKMB.Model.ToSeqChildren(children).1;
      {
        LKMB.Model.ToSeqChildrenAdditive(children[..i], children[i..]);
        assert children == children[..i] + children[i..];
      }
      csA + LKMB.Model.ToSeqChildren(children[i..]).1;
      {
        LKMB.Model.ToSeqChildrenAdditive(children[i..i+1], children[i+1..]);
        assert children[i..] == children[i..i+1] + children[i+1..];
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

    assert csB == [ LKMB.Model.ToSeq(children[i]).1 ];
    assert Flatten(csB) == LKMB.Model.ToSeq(children[i]).1 by {
      FlattenSingleton(LKMB.Model.ToSeq(children[i]).1);
    }

    assert forall m | m in LKMB.Model.ToSeq(children[i]).1 :: m in LKMB.Model.ToSeq(node).1;
    forall m | m in LKMB.Model.ToSeq(children[i]).1
      ensures ValueMessage.EncodableMessage(m)
    {
      LKMTreeEncodableToSeq(node);
    }
  }

  method LeafFillDpkv(shared node: LKMB.Model.Node, dpkv: DPKV.DynamicPkv)
    requires LKMB.WF(node)
    requires node.Leaf?
    requires dpkv.WF()
    requires IsKeyMessageTree(node)
    requires PKV.PSA.psaCanAppendSeq(dpkv.toPkv().keys, LKMB.Model.ToSeq(node).0)
    requires (LKMTreeEncodableToSeq(node); PKV.PSA.psaCanAppendSeq(dpkv.toPkv().messages, ValueMessage.messageSeq_to_bytestringSeq(LKMB.Model.ToSeq(node).1)))
    ensures dpkv.WF()
    ensures fresh(dpkv.Repr - old(dpkv.Repr))
    ensures dpkv.toPkv().keys == PKV.PSA.psaAppendSeq(old(dpkv.toPkv().keys), LKMB.Model.ToSeq(node).0)
    //ensures PKV.IKeys(dpkv.toPkv().keys) == old(PKV.IKeys(dpkv.toPkv().keys)) + LKMB.L.Model.ToSeq(node).0
    ensures dpkv.toPkv().messages == PKV.PSA.psaAppendSeq(old(dpkv.toPkv().messages), ValueMessage.messageSeq_to_bytestringSeq(LKMB.Model.ToSeq(node).1))
    //ensures PKV.IMessages(dpkv.toPkv().messages) == old(PKV.IMessages(dpkv.toPkv().messages)) + LKMB.L.Model.ToSeq(node).1
    modifies dpkv.Repr
  {
    LKMTreeEncodableToSeq(node); 
    shared var keys := node.keys;
    shared var values := node.values;
    var nkeys := seq_length(keys);
    
    assert LKMB.Model.ToSeq(node).0 == keys[..nkeys] by {
      LKMB.Model.reveal_ToSeq();
    }

    assert LKMB.Model.ToSeq(node).1 == values[..nkeys] by {
      LKMB.Model.reveal_ToSeq();
    }        

    forall i | 0 <= i < nkeys
      ensures keys[i] in LKMB.Interpretation(node)
    {
      LKMB.Model.reveal_Interpretation();
    }
    
    linear var messages := ValueMessage.MessageSeq_to_bytestringSeq(values, nkeys);
    linear var keys_nkeys := AllocAndCopy(keys, 0, nkeys);
    dpkv.keys.AppendSeq(keys_nkeys);
    //dpkv.keys.AppendSeq(keys[..nkeys]);
    dpkv.messages.AppendSeq(messages);
    dpkv.Repr := {dpkv} + dpkv.keys.Repr + dpkv.messages.Repr;
    var _ := seq_free(keys_nkeys);
    var _ := seq_free(messages);
  }

  lemma canAppendKeysIterate(pkv: PKV.Pkv, keyseqs: seq<seq<LKMB.Model.Key>>)
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
  
  lemma canAppendMessagesIterate(pkv: PKV.Pkv, msgseqs: seq<seq<LKMB.Model.Messages.Message>>)
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
  
  // TODO(robj): Break this monster up.
  method IndexFillDpkv(shared node: LKMB.Model.Node, dpkv: DPKV.DynamicPkv)
    requires LKMB.WF(node)
    requires node.Index?
    requires dpkv.WF()
    requires IsKeyMessageTree(node)
    requires PKV.PSA.psaCanAppendSeq(dpkv.toPkv().keys, LKMB.Model.ToSeq(node).0)
    requires (LKMTreeEncodableToSeq(node); PKV.PSA.psaCanAppendSeq(dpkv.toPkv().messages, ValueMessage.messageSeq_to_bytestringSeq(LKMB.Model.ToSeq(node).1)))
    ensures dpkv.WF()
    ensures fresh(dpkv.Repr - old(dpkv.Repr))
    ensures dpkv.toPkv().keys == PKV.PSA.psaAppendSeq(old(dpkv.toPkv().keys), LKMB.Model.ToSeq(node).0)
    ensures dpkv.toPkv().messages == PKV.PSA.psaAppendSeq(old(dpkv.toPkv().messages), ValueMessage.messageSeq_to_bytestringSeq(LKMB.Model.ToSeq(node).1))
    modifies dpkv.Repr
    decreases node, 0
  {
    ghost var children := lseqs(node.children);
    var nchildren := lseq_length_uint64(node.children);

    ghost var childSeqs := LKMB.Model.ToSeqChildren(children);
    assert forall i | 0 <= i < |childSeqs.0| :: childSeqs.0[i] == LKMB.Model.ToSeq(children[i]).0 by {
      LKMB.Model.reveal_ToSeq();
    }
    assert forall i | 0 <= i < |childSeqs.1| :: childSeqs.1[i] == LKMB.Model.ToSeq(children[i]).1 by {
      LKMB.Model.reveal_ToSeq();
    }

    assert Flatten(childSeqs.0) == LKMB.Model.ToSeq(node).0 by {
      LKMB.Model.reveal_ToSeq();
    }
    assert Flatten(childSeqs.1) == LKMB.Model.ToSeq(node).1 by {
      LKMB.Model.reveal_ToSeq();
    }
    LKMTreeEncodableToSeq(node);
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
      assert LKMB.WF(children[i]);
      assert dpkv.WF();
//      assert children[i].repr !! dpkv.Repr;

      IsKeyMessageTreeInheritance(node, i as nat);
      assert IsKeyMessageTree(children[i]);

      canAppendKeysIterate(dpkv.toPkv(), childSeqs.0[i..]);
      canAppendMessagesIterate(dpkv.toPkv(), childSeqs.1[i..]);

      ghost var prekeys := dpkv.toPkv().keys;
      ghost var premsgs := dpkv.toPkv().messages;

      assert PKV.PSA.psaCanAppendSeq(dpkv.toPkv().keys, LKMB.Model.ToSeq(children[i]).0);
      assume false;
      FillDpkv(lseq_peek(node.children, i), dpkv);
      
      calc {
        dpkv.toPkv().keys;
        PKV.PSA.psaAppendSeq(prekeys, LKMB.Model.ToSeq(children[i]).0);
        PKV.PSA.psaAppendSeq(PKV.PSA.psaAppendSeq(oldpkvkeys, Flatten(childSeqs.0[..i])), LKMB.Model.ToSeq(children[i]).0);
        { PKV.PSA.psaAppendSeqAdditive(oldpkvkeys, Flatten(childSeqs.0[..i]), LKMB.Model.ToSeq(children[i]).0); }
        PKV.PSA.psaAppendSeq(oldpkvkeys, Flatten(childSeqs.0[..i]) + LKMB.Model.ToSeq(children[i]).0);
        PKV.PSA.psaAppendSeq(oldpkvkeys, Flatten(childSeqs.0[..i]) + childSeqs.0[i]);
        { FlattenSingleton(childSeqs.0[i]); }
        PKV.PSA.psaAppendSeq(oldpkvkeys, Flatten(childSeqs.0[..i]) + Flatten([ childSeqs.0[i] ]));
        { FlattenAdditive(childSeqs.0[..i], [ childSeqs.0[i] ]); }
        PKV.PSA.psaAppendSeq(oldpkvkeys, Flatten(childSeqs.0[..i] + [ childSeqs.0[i] ]));
        assert childSeqs.0[..i+1] == childSeqs.0[..i] + [ childSeqs.0[i] ];
        PKV.PSA.psaAppendSeq(oldpkvkeys, Flatten(childSeqs.0[..i+1]));
      }

    
      calc {
        dpkv.toPkv().messages;
        PKV.PSA.psaAppendSeq(premsgs, ValueMessage.messageSeq_to_bytestringSeq(LKMB.Model.ToSeq(children[i]).1));
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
        assert childSeqs.1[..i+1] == childSeqs.1[..i] + [ childSeqs.1[i] ];
        PKV.PSA.psaAppendSeq(oldpkvmsgs, ValueMessage.messageSeq_to_bytestringSeq(Flatten(childSeqs.1[..i+1])));
      }
      
      i := i + 1;
    }

    calc {
      dpkv.toPkv().keys;
      PKV.PSA.psaAppendSeq(oldpkvkeys, Flatten(childSeqs.0[..i]));
      { assert childSeqs.0[..i] == childSeqs.0; }
      PKV.PSA.psaAppendSeq(old(dpkv.toPkv().keys), LKMB.Model.ToSeq(node).0);
    }
    calc {
      dpkv.toPkv().messages;
      PKV.PSA.psaAppendSeq(oldpkvmsgs, ValueMessage.messageSeq_to_bytestringSeq(Flatten(childSeqs.1[..i])));
      { assert childSeqs.1[..i] == childSeqs.1; }
      PKV.PSA.psaAppendSeq(old(dpkv.toPkv().messages), ValueMessage.messageSeq_to_bytestringSeq(LKMB.Model.ToSeq(node).1));
    }
  }

  method FillDpkv(shared node: LKMB.Model.Node, dpkv: DPKV.DynamicPkv)
    requires LKMB.WF(node)
    requires dpkv.WF()
    requires IsKeyMessageTree(node)
    requires PKV.PSA.psaCanAppendSeq(dpkv.toPkv().keys, LKMB.Model.ToSeq(node).0)
    requires (LKMTreeEncodableToSeq(node); PKV.PSA.psaCanAppendSeq(dpkv.toPkv().messages, ValueMessage.messageSeq_to_bytestringSeq(LKMB.Model.ToSeq(node).1)))
    ensures dpkv.WF()
    ensures fresh(dpkv.Repr - old(dpkv.Repr))
    ensures dpkv.toPkv().keys == PKV.PSA.psaAppendSeq(old(dpkv.toPkv().keys), LKMB.Model.ToSeq(node).0)
    ensures dpkv.toPkv().messages == PKV.PSA.psaAppendSeq(old(dpkv.toPkv().messages), ValueMessage.messageSeq_to_bytestringSeq(LKMB.Model.ToSeq(node).1))
    modifies dpkv.Repr
    decreases node, 1
  {
    if node.Leaf? {
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
  
  lemma ToSeqInterpretation(node: LKMB.Model.Node)
    requires LKMB.WF(node)
    requires IsKeyMessageTree(node)
    ensures forall k | k in LKMB.Model.ToSeq(node).0 :: |k| <= KeyType.MaxLen() as nat
    ensures BucketsLib.Bucket(byteSeqSeqToKeySeq(LKMB.Model.ToSeq(node).0), LKMB.Model.ToSeq(node).1).as_map() == LKMB.Interpretation(node)
  {
    LKMB.Model.ToSeqCoversInterpretation(node);
    LKMB.Model.ToSeqInInterpretation(node);
    assert forall k | k in LKMB.Model.ToSeq(node).0 :: k in LKMB.Interpretation(node);
    var keys: seq<LKMB.Model.Key> := byteSeqSeqToKeySeq(LKMB.Model.ToSeq(node).0);
    var msgs := LKMB.Model.ToSeq(node).1;
    var interp := LKMB.Interpretation(node);
    LKMB.Model.ToSeqIsStrictlySorted(node);
    assert LKMB.Model.Keys.IsStrictlySorted(keys) by {
      LKMB.Model.Keys.reveal_IsStrictlySorted();
    }
    calc {
      BucketsLib.Bucket(byteSeqSeqToKeySeq(LKMB.Model.ToSeq(node).0), LKMB.Model.ToSeq(node).1).as_map();
      MapSeqs.map_of_seqs(byteSeqSeqToKeySeq(LKMB.Model.ToSeq(node).0), LKMB.Model.ToSeq(node).1);
      {
        MapSeqs.eq_map_of_seqs(keys, msgs, interp);
      }
      LKMB.Interpretation(node);
    }
  }

  lemma IMessagesInverse(pkv: PKV.Pkv, msgs: seq<LKMB.Model.Messages.Message>)
    requires PKV.WF(pkv)
    requires ValueMessage.EncodableMessageSeq(msgs)
    requires PKV.PSA.I(pkv.messages) == ValueMessage.messageSeq_to_bytestringSeq(msgs)
    ensures PKV.IMessages(pkv.messages) == msgs
  {
    
  }

  lemma ToPkvPreservesInterpretation(node: LKMB.Model.Node, pkv: DPKV.PKV.Pkv)
    requires LKMB.WF(node)
    requires IsKeyMessageTree(node)
    requires PKV.PSA.psaCanAppendSeq(PKV.PSA.EmptyPsa(), LKMB.Model.ToSeq(node).0)
    requires (LKMTreeEncodableToSeq(node); PKV.PSA.psaCanAppendSeq(PKV.PSA.EmptyPsa(), ValueMessage.messageSeq_to_bytestringSeq(LKMB.Model.ToSeq(node).1)))
    requires DPKV.PKV.WF(pkv)
    requires PKV.IKeys(pkv.keys) == LKMB.Model.ToSeq(node).0
    requires PKV.PSA.I(pkv.messages) == ValueMessage.messageSeq_to_bytestringSeq(LKMB.Model.ToSeq(node).1)
    ensures DPKV.PKV.I(pkv) == BucketsLib.B(LKMB.Interpretation(node))
  {
    LKMTreeEncodableToSeq(node);
    var keys := byteSeqSeqToKeySeq(LKMB.Model.ToSeq(node).0);
    var msgs := LKMB.Model.ToSeq(node).1;
    calc {
      DPKV.PKV.I(pkv).as_map();
      BucketsLib.Bucket(PKV.IKeys(pkv.keys), PKV.IMessages(pkv.messages)).as_map();
      { assert PKV.IKeys(pkv.keys) == keys; }
      BucketsLib.Bucket(keys, PKV.IMessages(pkv.messages)).as_map();
      { IMessagesInverse(pkv, msgs); }
      BucketsLib.Bucket(keys, msgs).as_map();
      { ToSeqInterpretation(node); }
      LKMB.Interpretation(node);
      BucketsLib.B(LKMB.Interpretation(node)).as_map();
    }
    LKMB.Model.ToSeqIsStrictlySorted(node);
    BucketsLib.WellMarshalledBucketsEq(DPKV.PKV.I(pkv), BucketsLib.B(LKMB.Interpretation(node)));
  }

  lemma WeightImpliesCanAppend(node: LKMB.Node)
    requires LKMB.WF(node)
    requires IsKeyMessageTree(node)
    requires BucketWeights.WeightBucket(BucketsLib.B(LKMB.Interpretation(node))) < Uint32UpperBound()
    ensures (LKMTreeEncodableToSeq(node); PKV.PSA.psaCanAppendSeq(PKV.PSA.EmptyPsa(), LKMB.Model.ToSeq(node).0))
    ensures PKV.PSA.psaCanAppendSeq(PKV.PSA.EmptyPsa(), ValueMessage.messageSeq_to_bytestringSeq(LKMB.Model.ToSeq(node).1))
  {
    LKMB.Model.ToSeqInInterpretation(node);
    var keys := byteSeqSeqToKeySeq(LKMB.Model.ToSeq(node).0);
    var msgs := LKMB.Model.ToSeq(node).1;
    var interp := LKMB.Interpretation(node);
    var bucket := BucketsLib.Bucket(keys, msgs);
    ToSeqInterpretation(node);
    LKMB.Model.ToSeqIsStrictlySorted(node);
    
    BucketWeights.NumElementsLteWeight(BucketsLib.B(interp));
    LKMB.Model.InterpretationNumElements(node);
    LKMB.Model.ToSeqLength(node);

    BucketsLib.WellMarshalledBucketsEq(bucket, BucketsLib.B(interp));

    BucketWeights.WeightKeyListFlatten(keys);
    assert keys == BucketsLib.B(interp).keys;

    BucketWeights.WeightMessageListFlatten(msgs);
    assert msgs == BucketsLib.B(interp).msgs;
  }

  method ToPkv(shared node: LKMB.Model.Node) returns (pkv: DPKV.PKV.Pkv)
    requires LKMB.WF(node)
    requires IsKeyMessageTree(node)
    requires (LKMTreeEncodableToSeq(node); PKV.PSA.psaCanAppendSeq(PKV.PSA.EmptyPsa(), LKMB.Model.ToSeq(node).0))
    requires PKV.PSA.psaCanAppendSeq(PKV.PSA.EmptyPsa(), ValueMessage.messageSeq_to_bytestringSeq(LKMB.Model.ToSeq(node).1))
    ensures DPKV.PKV.WF(pkv)
    ensures PKV.IKeys(pkv.keys) == LKMB.Model.ToSeq(node).0
    ensures PKV.PSA.I(pkv.messages) == ValueMessage.messageSeq_to_bytestringSeq(LKMB.Model.ToSeq(node).1)
    ensures DPKV.PKV.I(pkv) == BucketsLib.B(LKMB.Interpretation(node))
  {
    LKMB.Model.ToSeqLength(node);
    var nelts: uint64 := LKMB.CountElements(node);
    var keydatasize := if nelts * KeyType.MaxLen() <= 0xffff_ffff then (nelts * KeyType.MaxLen()) as uint32 else 0xffff_ffff;
    var msgdatasize := if nelts * ValueType.MaxLen() <= 0xffff_ffff then (nelts * ValueType.MaxLen()) as uint32 else 0xffff_ffff;
    var cap := DPKV.Capacity(nelts as uint32, keydatasize, msgdatasize);
    var dpkv := new DPKV.DynamicPkv.PreSized(cap);
    FillDpkv(node, dpkv);
    pkv := dpkv.toPkv();
    ToPkvPreservesInterpretation(node, pkv);
  }

  // I don't think we use this much (if at all?) so not optimizing for now.
  method FromPkv(pkv: DPKV.PKV.Pkv) returns (linear node: LKMB.Node, weight: uint64)
    requires DPKV.PKV.WF(pkv)
    ensures LKMB.WF(node)
    ensures IsKeyMessageTree(node)
    ensures PKV.I(pkv).as_map() == LKMB.Interpretation(node)
    ensures weight as nat == BucketWeights.WeightBucket(BucketsLib.B(LKMB.Interpretation(node)))
  {
    ghost var keys := PKV.IKeys(pkv.keys);
    ghost var msgs := PKV.IMessages(pkv.messages);
    
    var i: uint64 := 0;
    var oldvalue;
    
    node := LKMB.EmptyTree();
    weight := 0;

    BucketsLib.B_empty_map();
    
    while i < DPKV.PKV.NumKVPairs(pkv)
      invariant i <= DPKV.PKV.NumKVPairs(pkv)
      invariant LKMB.WF(node)
      invariant IsKeyMessageTree(node)
      invariant LKMB.Interpretation(node) == BucketsLib.Bucket(keys[..i], msgs[..i]).as_map()
      invariant weight as nat == BucketWeights.WeightBucket(BucketsLib.B(LKMB.Interpretation(node)))
    {
      calc <= {
        weight as nat;
        BucketWeights.WeightBucket(BucketsLib.B(LKMB.Interpretation(node)));
        BucketWeights.WeightBucket(BucketsLib.B(BucketsLib.Bucket(keys[..i], msgs[..i]).as_map()));
        { BucketWeights.Weight_Bucket_eq_BucketMap(BucketsLib.Bucket(keys[..i], msgs[..i]).as_map()); }
        BucketWeights.WeightBucketMap(BucketsLib.Bucket(keys[..i], msgs[..i]).as_map());
        { BucketWeights.Weight_BucketMap_le_Bucket(BucketsLib.Bucket(keys[..i], msgs[..i])); }
        BucketWeights.WeightBucket(BucketsLib.Bucket(keys[..i], msgs[..i]));
        {
          assert keys == keys[..i] + keys[i..];
          assert msgs == msgs[..i] + msgs[i..];
          BucketWeights.WeightKeyListAdditive(keys[..i], keys[i..]);
          BucketWeights.WeightMessageListAdditive(msgs[..i], msgs[i..]);
        }
        BucketWeights.WeightBucket(BucketsLib.Bucket(keys, msgs));
        BucketWeights.WeightBucket(PKV.I(pkv));
        {
          DPKV.WeightBucketPkv_eq_WeightPkv(pkv);
        }
        PKV.WeightPkv(pkv) as nat;
        0x10_0000_0000;
      }
      ghost var oldinterp := LKMB.Interpretation(node);
      ghost var oldweight := weight as nat;
      
      var key := DPKV.PKV.GetKey(pkv, i);
      var msg := DPKV.PKV.GetMessage(pkv, i);
      node, oldvalue := LKMB.Insert(node, key, msg);

      weight := weight + BucketWeights.WeightMessageUint64(msg);
      if oldvalue.Some? {
        calc <= {
          BucketWeights.WeightMessageUint64(oldvalue.value) as nat;
          { BucketWeights.WeightBucketMapSingleton(key, oldvalue.value); }
          BucketWeights.WeightBucketMap(map[key := oldvalue.value]);
          {
            BucketWeights.WeightBucketMapSubsetLe(map[key := oldvalue.value], oldinterp);
          }
          BucketWeights.WeightBucketMap(oldinterp);
          {
            BucketWeights.Weight_Bucket_eq_BucketMap(oldinterp);
          }
          BucketWeights.WeightBucket(BucketsLib.B(oldinterp));
          oldweight;
          weight as nat;
        }
        weight := weight - BucketWeights.WeightMessageUint64(oldvalue.value);

        ghost var map0 := Maps.MapRemove1(oldinterp, key);
        BucketWeights.WeightBucketInduct(map0, key, oldvalue.value);
        BucketWeights.WeightBucketInduct(map0, key, msg);
        assert oldinterp == map0[key := oldvalue.value];
        assert LKMB.Interpretation(node) == map0[key := msg];
      } else {
        weight := weight + BucketWeights.WeightKeyUint64(key);
        BucketWeights.WeightBucketInduct(oldinterp, key, msg);
      }

      MapSeqs.induct_map_of_seqs(keys[..i+1], msgs[..i+1]);
      assert keys[..i+1] == keys[..i] + [ keys[i] ];
      assert msgs[..i+1] == msgs[..i] + [ msgs[i] ];

      i := i + 1;

      BucketWeights.Weight_Bucket_eq_BucketMap(oldinterp);
      BucketWeights.Weight_Bucket_eq_BucketMap(LKMB.Interpretation(node));
    }

    assert keys[..i] == keys;
    assert msgs[..i] == msgs;
  }
}
