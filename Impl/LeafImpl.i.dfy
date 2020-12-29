include "BookkeepingImpl.i.dfy"
include "LeafModel.i.dfy"

module LeafImpl { 
  import opened IOImpl
  import opened BookkeepingImpl
  import opened LeafModel
  import opened StateBCImpl
  import opened NodeImpl
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

  import IT = IndirectionTable

  import opened NativeTypes

  method CopyKey(k: KeyType.Key) returns (k2: KeyType.Key)
  ensures k2 == k
  {
    k2 := [] + k;
  }

  method repivotLeaf(s: ImplVariables, ref: BT.G.Reference)
  requires Inv(s)
  requires s.ready
  requires ref in s.ephemeralIndirectionTable.I().graph
  requires s.cache.ptr(ref).Some?
  requires s.cache.I()[ref].children.None?
  requires |s.cache.I()[ref].buckets| == 1
  requires |s.ephemeralIndirectionTable.I().graph| <= IT.MaxSize() - 1
  modifies s.Repr()
  ensures s.ready
  ensures WellUpdated(s)
  ensures s.I() == LeafModel.repivotLeaf(old(s.I()), ref, old(s.cache.I()[ref]));
  {
    LeafModel.reveal_repivotLeaf();

    if s.frozenIndirectionTable != null {
      var b := s.frozenIndirectionTable.HasEmptyLoc(ref);
      if b {
        print "giving up; repivotLeaf can't run because frozen isn't written";
        return;
      }
    }

    var bounded := s.cache.NodeBoundedBucket(ref, ref, 0);
    ghost var buckets := s.cache.I()[ref].buckets;
    assert bounded == BoundedBucketList(buckets, s.cache.I()[ref].pivotTable);
    if !bounded {
      print "giving up; repivotLeaf can't run because current leaf is incorrect";
      return;
    }

    var pivot: KeyType.Key;
    linear var left, right;
    var pivots := InitPivotTable();

    left, right, pivot := s.cache.NodeSplitMiddle(ref);
    linear var buckets' := lseq_alloc(2);
    lseq_give_inout(inout buckets', 0, left);
    lseq_give_inout(inout buckets', 1, right);

    pivot := CopyKey(pivot);
    pivots := Insert(pivots, Keyspace.Element(pivot), 1);

    linear var newnode := Node(pivots, None, buckets');
    writeBookkeeping(s, ref, None);
    s.cache.Insert(ref, newnode);
    assert s.W();

    ghost var a := s.I();
    ghost var oldnode := old(s.cache.I()[ref]);
    ghost var b := LeafModel.repivotLeaf(old(s.I()), ref, oldnode);
    assert newnode.I() == old(BT.G.Node(pivots, None, [
          SplitBucketLeft(oldnode.buckets[0], pivot),
          SplitBucketRight(oldnode.buckets[0], pivot)
        ]));
    assert a.cache == b.cache;
  }
}
