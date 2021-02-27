// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

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

  method repivotLeaf(linear inout s: ImplVariables, ref: BT.G.Reference)
  requires old_s.Inv()
  requires old_s.Ready?
  requires ref in old_s.ephemeralIndirectionTable.I().graph
  requires old_s.cache.ptr(ref).Some?
  requires old_s.cache.I()[ref].children.None?
  requires |old_s.cache.I()[ref].buckets| == 1
  requires |old_s.ephemeralIndirectionTable.I().graph| <= IT.MaxSize() - 1
  ensures s.Ready?
  ensures s.W()
  ensures s.I() == LeafModel.repivotLeaf(old_s.I(), ref, old_s.cache.I()[ref]);
  {
    LeafModel.reveal_repivotLeaf();
    var b := false;

    if s.frozenIndirectionTable.lSome? {
      b := s.frozenIndirectionTable.value.HasEmptyLoc(ref);
    }

    if b {
      print "giving up; repivotLeaf can't run because frozen isn't written";
    } else {
      var bounded := s.cache.NodeBoundedBucket(ref, ref, 0);
      ghost var buckets := s.cache.I()[ref].buckets;
      assert bounded == BoundedBucketList(buckets, s.cache.I()[ref].pivotTable);
      if !bounded {
        print "giving up; repivotLeaf can't run because current leaf is incorrect";
      } else {
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
        writeBookkeeping(inout s, ref, None);
        inout s.cache.Insert(ref, newnode);
        assert s.W();

        ghost var a := s.I();
        ghost var oldnode := old_s.cache.I()[ref];
        ghost var b := LeafModel.repivotLeaf(old_s.I(), ref, oldnode);
        assert newnode.I() == BT.G.Node(pivots, None, [
              SplitBucketLeft(oldnode.buckets[0], pivot),
              SplitBucketRight(oldnode.buckets[0], pivot)
            ]);
        assert a.cache == b.cache;
      }
    }
  }
}
