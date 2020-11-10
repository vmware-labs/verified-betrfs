include "BookkeepingImpl.i.dfy"
include "LeafModel.i.dfy"

module LeafImpl { 
  import opened IOImpl
  import opened BookkeepingImpl
  import opened LeafModel
  import opened StateImpl
  import opened BoxNodeImpl
  import opened BucketImpl
  import opened DiskOpImpl

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets
  import opened LinearSequence_s
  import opened LinearSequence_i
  import opened BucketsLib
  import opened BoundedPivotsLib

  import opened NativeTypes

  method CopyKey(k: KeyType.Key) returns (k2: KeyType.Key)
  ensures k2 == k
  {
    k2 := [] + k;
  }

  method repivotLeaf(s: ImplVariables, ref: BT.G.Reference, node: Node)
  requires Inv(s)
  requires s.ready
  requires ref in s.ephemeralIndirectionTable.I().graph
  requires s.cache.ptr(ref) == Some(node)
  requires node.Inv()
  requires node.Read().children.None?
  requires |node.Read().buckets| == 1
  requires |s.ephemeralIndirectionTable.I().graph| <= IndirectionTableModel.MaxSize() - 1
  modifies s.Repr()
  ensures s.ready
  ensures WellUpdated(s)
  ensures s.I() == LeafModel.repivotLeaf(old(s.I()), ref, old(node.I()));
  {
    LeafModel.reveal_repivotLeaf();

    if s.frozenIndirectionTable != null {
      var b := s.frozenIndirectionTable.HasEmptyLoc(ref);
      if b {
        print "giving up; repivotLeaf can't run because frozen isn't written";
        return;
      }
    }

    var oldpivots := node.GetPivots();
    var bounded := node.BoundedBucket(oldpivots, 0);
    
    ghost var buckets := node.I().buckets;
    assert bounded == BoundedBucketList(buckets, oldpivots);

    if !bounded {
      print "giving up; repivotLeaf can't run because current leaf is incorrect";
      return;
    }

    var pivot := lseq_peek(node.box.Borrow().buckets, 0).GetMiddleKey();
    pivot := CopyKey(pivot);
    var pivots := InitPivotTable();
    pivots := Insert(pivots, Keyspace.Element(pivot), 1);

    linear var left, right := MutBucket.SplitLeftRight(lseq_peek(node.box.Borrow().buckets, 0), pivot);
    linear var buckets' := lseq_alloc(2);
    lseq_give_inout(inout buckets', 0, left);
    lseq_give_inout(inout buckets', 1, right);

    var newnode := new Node(pivots, None, buckets');

    writeBookkeeping(s, ref, None);

    assert fresh(newnode.Repr);
    assert s.cache.Repr !! newnode.Repr;
    s.cache.Insert(ref, newnode);

    assert s.W();

    ghost var a := s.I();
    ghost var b := LeafModel.repivotLeaf(old(s.I()), ref, old(node.I()));
    assert newnode.I() == old(BT.G.Node(pivots, None, [
          SplitBucketLeft(node.I().buckets[0], pivot),
          SplitBucketRight(node.I().buckets[0], pivot)
        ]));
      
    assert a.cache == b.cache;
  }
}
