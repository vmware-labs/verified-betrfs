// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "BucketIteratorModel.i.dfy"
include "../lib/Buckets/TranslationImpl.i.dfy"

module BucketIteratorImpl {
  import BucketIteratorModel
  import opened Options
  import opened Sequences
  import opened NativeTypes
  import opened KeyType
  import opened BucketsLib
  import opened BucketImpl
  import opened TranslationLib
  import opened TranslationImpl

  datatype Iterator = Iterator(
    pset: Option<PrefixSet>,
    ghost next: BucketIteratorModel.IteratorOutput,
    i: uint64,
    ghost decreaser: int)

  function IIterator(it: Iterator) : BucketIteratorModel.Iterator
  {
    BucketIteratorModel.Iterator(it.pset, it.next, it.i as int, it.decreaser)
  }

  linear datatype BucketIter = BucketIter(it: Iterator, pkv: PackedKV.Pkv, ghost bucket: Bucket)
  {
    predicate WFIter()
    {
      && PackedKV.WF(pkv)
      && bucket == PackedKV.I(pkv)
      && BucketIteratorModel.WFIter(bucket, IIterator(it))
    } 

    linear method Free()
    {
      linear var BucketIter(_,_,_) := this;
    }

    static function method makeIter(ghost bucket: Bucket, pset: Option<PrefixSet>, idx: uint64): (it': Iterator)
    requires WFBucket(bucket)
    requires |bucket.keys| == |bucket.msgs|
    requires 0 <= idx as int <= |bucket.keys|
    requires idx as int < |bucket.keys| && pset.Some? 
        ==> IsPrefix(pset.value.prefix, bucket.keys[idx])
    ensures IIterator(it')
      == BucketIteratorModel.iterForIndex(bucket, pset, idx as int)
    {
      Iterator(
          pset,
          (if idx as int == |bucket.keys| then BucketIteratorModel.Done
              else BucketIteratorModel.Next(ApplyPrefixSet(pset, bucket.keys[idx]), bucket.msgs[idx])),
          idx,
          |bucket.keys| - idx as int)
    }

    static method IterNextWithPrefix(ghost bucket: Bucket, pkv: PackedKV.Pkv, prefix: Key, idx: uint64) returns (i: uint64)
    requires WFBucket(bucket)
    requires PackedKV.WF(pkv)
    requires PackedKV.I(pkv) == bucket
    requires 0 <= idx as int <= |bucket.keys|
    ensures idx as int <= i as int <= |bucket.keys|
    ensures i as int == BucketIteratorModel.iterNextWithPrefix(bucket, prefix, idx as int)
    {
      var len := PackedKV.NumKVPairs(pkv);
      if idx < len {
        var key : Key := PackedKV.GetKey(pkv, idx);
        var isprefix := |prefix| as uint64 <= |key| as uint64 && prefix == key[..|prefix|];
        reveal_IsPrefix();

        if isprefix {
          return idx;
        } 

        var c := PackedKV.KeyspaceImpl.cmp(key, prefix);
        if c < 0 {
          var i := PackedKV.PSA.BinarySearchIndexOfFirstKeyGteWithLowerBound(pkv.keys, prefix, idx+1);
          if i < len {
            key := PackedKV.GetKey(pkv, i);
            isprefix := |prefix| as uint64 <= |key| as uint64 && prefix == key[..|prefix|];
            if isprefix {
              return i;
            }
          }
        }
      }
      return len;
    }

    static method IterStart(shared bucket: MutBucket, pset: Option<PrefixSet>) returns (linear biter: BucketIter)
    requires bucket.Inv()
    ensures biter.WFIter()
    ensures biter.bucket == bucket.I()
    ensures IIterator(biter.it) == BucketIteratorModel.IterStart(biter.bucket, pset)
    {
      BucketIteratorModel.reveal_IterStart();

      ghost var b := bucket.I();
      var pkv := bucket.GetPkv();

      var i;
      if pset.None? {
        i := 0;
      } else {
        i := IterNextWithPrefix(bucket.bucket, pkv, pset.value.prefix, 0);
      }

      var it := makeIter(b, pset, i);
      biter := BucketIter(it, pkv, b);
    }

    static method IterFindFirstGte(shared bucket: MutBucket, pset: Option<PrefixSet>, key': Key)
    returns (linear biter: BucketIter)
    requires bucket.Inv()
    requires pset.Some? ==> IsPrefix(pset.value.prefix, key')
    ensures biter.WFIter()
    ensures biter.bucket == bucket.I()
    ensures IIterator(biter.it) == BucketIteratorModel.IterFindFirstGte(biter.bucket, pset, ApplyPrefixSet(pset, key'))
    {
      BucketIteratorModel.reveal_IterFindFirstGte();
      ghost var b := bucket.I();
      var pkv := bucket.GetPkv();

      ghost var key := ApplyPrefixSet(pset, key');
      assert ApplyPrefixSet(RevPrefixSet(pset), key) == key' by { reveal_IsPrefix(); }

      var i: uint64 := PackedKV.PSA.BinarySearchIndexOfFirstKeyGte(pkv.keys, key');  
      if pset.Some? {
        i := IterNextWithPrefix(bucket.bucket, pkv, pset.value.prefix, i);
      }

      var it := makeIter(b, pset, i);
      biter := BucketIter(it, pkv, b);
    }

    static method IterFindFirstGt(shared bucket: MutBucket, pset: Option<PrefixSet>, key': Key) returns (linear biter: BucketIter)
    requires bucket.Inv()
    requires pset.Some? ==> IsPrefix(pset.value.prefix, key')
    ensures biter.WFIter()
    ensures biter.bucket == bucket.I()
    ensures IIterator(biter.it) == BucketIteratorModel.IterFindFirstGt(biter.bucket, pset, ApplyPrefixSet(pset, key'))
    {
      BucketIteratorModel.reveal_IterFindFirstGt();
      ghost var b := bucket.I();
      var pkv := bucket.GetPkv();

      ghost var key := ApplyPrefixSet(pset, key');
      assert ApplyPrefixSet(RevPrefixSet(pset), key) == key' by { reveal_IsPrefix(); }

      var i: uint64 := PackedKV.PSA.BinarySearchIndexOfFirstKeyGt(pkv.keys, key');
      if pset.Some? {
        i := IterNextWithPrefix(bucket.bucket, pkv, pset.value.prefix, i);
      }

      var it := makeIter(b, pset, i);
      biter := BucketIter(it, pkv, b);
    }

    linear inout method IterInc()
    requires old_self.WFIter()
    requires IIterator(old_self.it).next.Next?
    ensures self.WFIter()
    ensures old_self.bucket == self.bucket
    ensures IIterator(self.it) == BucketIteratorModel.IterInc(old_self.bucket, IIterator(old_self.it))
    {
      BucketIteratorModel.lemma_NextFromIndex(self.bucket, IIterator(self.it));
      BucketIteratorModel.reveal_IterInc();

      var i;
      if self.it.pset.None? {
        i := self.it.i + 1;
      } else {
        i := IterNextWithPrefix(self.bucket, self.pkv, self.it.pset.value.prefix, self.it.i+1);
      }

      inout self.it := makeIter(self.bucket, self.it.pset, i);
    }

    shared method GetNext() returns (next : BucketIteratorModel.IteratorOutput)
    requires this.WFIter()
    ensures next == IIterator(this.it).next
    {
      BucketIteratorModel.lemma_NextFromIndex(bucket, IIterator(it));
        
      if it.i == |pkv.keys.offsets| as uint64 {
        next := BucketIteratorModel.Done;
      } else {
        var key := PackedKV.GetKey(pkv, it.i);
        var msg := PackedKV.GetMessage(pkv, it.i);
        next := BucketIteratorModel.Next(ApplyPrefixSet(it.pset, key), msg);
      }
    }
  }

}