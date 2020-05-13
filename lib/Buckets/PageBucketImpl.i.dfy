include "../../PivotBetree/Bounds.i.dfy"
include "BucketModel.i.dfy"
include "PackedKV.i.dfy"

// TODO(robj): convert this back to using member methods on
// datastructs once the C++ backend supports them.  Errors we were getting:

// build/Bundle.cpp:6749:60: error: member reference type 'PageBucketImpl_Compile::PageBucket' is not a
//      pointer; did you mean to use '.'?
//      auto _outcollector169 = (((this->page).dtor_value()))->ToPkv();
//                              ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~^~


module PageBucketImpl {
  import opened NativeTypes
  import opened BucketModel
  import opened KeyType
  //import opened ValueType`Internal
  import opened ValueMessage
  import opened Options
  import opened NativeArrays
  import PackedKV
  import DynamicPkv
  import KeyspaceImpl = Lexicographic_Byte_Order_Impl
  import opened Sequences
  import Uint32_Order
  
  function method PageSize() : uint64 { 4096 }  // XXX move to bounds

  method minUint64(a:uint64, b:uint64) returns (result:uint64)
    ensures a < b ==> result == a
    ensures b <= a ==> result == b
  {
    if a < b {
      result := a;
    } else {
      result := b;
    }
  }

  datatype PageBucketStore = PageBucketStore(
    bucketOffsets: seq<uint32>, // units: kvpairs. Last entry == |keyOffsets|==|valueOffsets|
    keyOffsets:seq<uint32>,     // units: bytes
    valueOffsets:seq<uint32>,   // units: bytes
    pages:seq<seq<byte>>)

  function AllocLen(this_: PageBucketStore) : nat
  {
    |this_.pages| * PageSize() as nat
  }
    
  function Data(this_: PageBucketStore) : seq<byte>
  {
    Flatten(this_.pages)
  }

  predicate AllPagesOfCorrectSize(pages: seq<seq<byte>>)
  {
    && (forall i | 0 <= i < |pages| :: |pages[i]| == PageSize() as nat)
  }
  
  predicate WFStore(this_: PageBucketStore)
  {
    && |this_.bucketOffsets| < Uint64UpperBound()
    && |this_.keyOffsets| < Uint64UpperBound()
    && |this_.valueOffsets| < Uint64UpperBound()
    && |this_.pages| < Uint64UpperBound()
    
    && Uint32_Order.IsSorted(this_.bucketOffsets)
    && (0 < |this_.bucketOffsets| ==> this_.bucketOffsets[0] == 0)
    && (0 < |this_.bucketOffsets| ==> Last(this_.bucketOffsets) as nat == |this_.keyOffsets|)

    && Uint32_Order.IsSorted(this_.keyOffsets)
    && (0 < |this_.keyOffsets| ==> this_.keyOffsets[0] == 0)
    && (0 < |this_.keyOffsets| ==> Last(this_.keyOffsets) as nat <= AllocLen(this_))

    && Uint32_Order.IsSorted(this_.valueOffsets)
    && (0 < |this_.valueOffsets| ==> this_.valueOffsets[0] == Last(this_.keyOffsets))
    && (0 < |this_.valueOffsets| ==> Last(this_.valueOffsets) as nat <= AllocLen(this_))

    && AllPagesOfCorrectSize(this_.pages)

    && |this_.keyOffsets| == |this_.valueOffsets|
    && (0 < |this_.keyOffsets| ==> 0 < |this_.bucketOffsets|)
  }

  lemma DataIsAllocLen(pages: seq<seq<byte>>)
    requires AllPagesOfCorrectSize(pages)
    ensures |Flatten(pages)| == |pages| * PageSize() as nat
  {
    reveal_Flatten();
    if |pages| == 0 {
    } else {
      DataIsAllocLen(DropLast(pages));
    }
  }

  lemma DataSliceIdentity(pages: seq<seq<byte>>, pageIdx: nat, offset: nat, len: nat)
    requires AllPagesOfCorrectSize(pages)
    requires pageIdx < |pages|
    requires offset + len <= PageSize() as nat
    ensures (DataIsAllocLen(pages);
             pages[pageIdx][offset..offset+len] ==
             Flatten(pages)[pageIdx * PageSize() as nat + offset..pageIdx * PageSize() as nat + offset + len])
  {
    reveal_Flatten();
    var pagesize := PageSize() as nat;
    var data := Flatten(pages);
    var data' := Flatten(DropLast(pages));
    assert data == data' + Last(pages);
    DataIsAllocLen(DropLast(pages));
    if pageIdx == |pages| - 1 {
      assert pages[pageIdx] == data[pageIdx * pagesize..pageIdx * pagesize + pagesize];
    } else {
      DataSliceIdentity(DropLast(pages), pageIdx, offset, len);
    }
  }
  
  method stitchBytes(this_: PageBucketStore, offset:uint64, len:uint64)
    returns (stitched: seq<byte>)
    requires WFStore(this_)
    requires offset as nat + len as nat <= AllocLen(this_)
  {
    DataIsAllocLen(this_.pages);
    ghost var data := Data(this_);
    
    var stitchedArray := new byte[len];
    var nextPage := offset / PageSize();
    var nextOffset := offset % PageSize();
    var nextLen := minUint64(PageSize() - nextOffset, len);
    var nextArrayOffset:uint64 := 0;
    var remainingLen := len;

    assert stitchedArray[..nextArrayOffset] == Data(this_)[offset..offset as nat + nextArrayOffset as nat];
    
    while 0 < nextLen
      invariant nextLen < remainingLen ==>
         (offset as nat + nextArrayOffset as nat + nextLen as nat) / PageSize() as nat
      == (offset as nat + nextArrayOffset as nat                 ) / PageSize() as nat + 1
      invariant 0 < nextLen ==> nextPage as nat == (offset as nat + nextArrayOffset as nat) / PageSize() as nat
      invariant nextOffset as nat + nextLen as nat <= PageSize() as nat
      invariant 0 < nextLen ==> nextOffset as nat == offset as nat + nextArrayOffset as nat - nextPage as nat * PageSize() as nat
      invariant nextArrayOffset as nat + remainingLen as nat == len as nat
      invariant nextArrayOffset as nat + nextLen as nat <= stitchedArray.Length
      invariant stitchedArray[..nextArrayOffset] == data[offset..offset as nat + nextArrayOffset as nat]
      decreases |this_.pages| - nextPage as nat
    {
      CopySeqIntoArray(this_.pages[nextPage], nextOffset as uint64, stitchedArray, nextArrayOffset as uint64, nextLen as uint64);
      assert stitchedArray[..nextArrayOffset+nextLen] ==
        stitchedArray[..nextArrayOffset] + stitchedArray[nextArrayOffset..nextArrayOffset+nextLen];
      assert data[offset..offset as nat + nextArrayOffset as nat + nextLen as nat] ==
        data[offset..offset as nat + nextArrayOffset as nat] +
        data[offset as nat + nextArrayOffset as nat..offset as nat + nextArrayOffset as nat + nextLen as nat];

      calc {
        stitchedArray[..nextArrayOffset+nextLen];
        stitchedArray[..nextArrayOffset] + stitchedArray[nextArrayOffset..nextArrayOffset+nextLen];
        data[offset..offset as nat + nextArrayOffset as nat] + stitchedArray[nextArrayOffset..nextArrayOffset+nextLen];
        data[offset..offset as nat + nextArrayOffset as nat] + this_.pages[nextPage][nextOffset..nextOffset+nextLen];
        { DataSliceIdentity(this_.pages, nextPage as nat, nextOffset as nat, nextLen as nat); }
        data[offset..offset as nat + nextArrayOffset as nat]
          + data[nextPage as nat * PageSize() as nat + nextOffset as nat..nextPage as nat * PageSize() as nat + nextOffset as nat + nextLen as nat];
        data[offset..offset as nat + nextArrayOffset as nat]
          + data[offset as nat + nextArrayOffset as nat..offset as nat + nextArrayOffset as nat + nextLen as nat];


        
        data[offset..offset as nat + nextArrayOffset as nat + nextLen as nat];
      }
        
      nextArrayOffset := nextArrayOffset + nextLen;
      remainingLen := remainingLen - nextLen;

      nextPage := nextPage + 1;
      nextOffset := 0;
      nextLen := minUint64(PageSize(), remainingLen);
    }
    return stitchedArray[..];
  }

  method getKey(this_: PageBucketStore, bucketIndex:uint64, kvIndexInBucket:uint64)
    returns (key: Key)
  {
    var kvIndex := this_.bucketOffsets[bucketIndex] as uint64 + kvIndexInBucket;
    var keyOffset := this_.keyOffsets[kvIndex] as uint64;
    var keyLen := this_.keyOffsets[kvIndex+1] as uint64 - keyOffset;
    key := stitchBytes(this_, keyOffset, keyLen);
  }

  method getValue(this_: PageBucketStore, bucketIndex:uint64, kvIndexInBucket:uint64)
    returns (value:seq<byte>)
  {
    var kvIndex := this_.bucketOffsets[bucketIndex] as uint64 + kvIndexInBucket;
    var valueOffset := this_.valueOffsets[kvIndex] as uint64;
    var valueLen := this_.valueOffsets[kvIndex+1] as uint64 - valueOffset;
    value := stitchBytes(this_, valueOffset, valueLen);
  }

  method getPkv(this_: PageBucketStore, bucketIndex: uint64) returns (result: PackedKV.Pkv)
  {
    var dpkv := new DynamicPkv.DynamicPkv.PreSized(DynamicPkv.EmptyCapacity());
    var i: uint64 := 0;
    var numPairs: uint64 := (this_.bucketOffsets[bucketIndex+1] - this_.bucketOffsets[bucketIndex]) as uint64;
    
    while i < numPairs
    {
      var key := getKey(this_, bucketIndex, i);
      var msgbytes := getValue(this_, bucketIndex, i);
      dpkv.AppendEncodedMessage(key, msgbytes);
      i := i + 1;
    }

    result := dpkv.toPkv();
  }
  
  datatype PageBucket = PageBucket(store:PageBucketStore, bucketIdx:uint64)

  method GetNumPairs(this_: PageBucket) returns (result:uint64) {
    result := this_.store.bucketOffsets[this_.bucketIdx + 1] as uint64
      - this_.store.bucketOffsets[this_.bucketIdx] as uint64;
  }

  method Query(this_: PageBucket, key: Key) returns (msg: Option<Message>)
  {
    var lo: uint64 := 0;
    var hi: uint64 := GetNumPairs(this_);
    while lo < hi
    {
      var mid: uint64 := (lo + hi) / 2;
      var midKey := getKey(this_.store, this_.bucketIdx, mid);
      var c := KeyspaceImpl.cmp(key, midKey);
      if c == 0 {
        var valueBytes := getValue(this_.store, this_.bucketIdx, mid);
        var message := PackedKV.bytestring_to_Message(valueBytes);
        msg := Some(message);
        return;
      } else if (c < 0) {
        hi := mid;
      } else {
        lo := mid + 1;
      }
    }
    msg := None;
  }

  method GetKey(this_: PageBucket, idx:uint64) returns (key:Key)
  {
    key := getKey(this_.store, this_.bucketIdx, idx);
  }

  method IsEmpty(this_: PageBucket) returns (empty: bool)
  {
    var numPairs := GetNumPairs(this_);
    empty := numPairs  == 0;
  }

  method ToPkv(this_: PageBucket) returns (pkv: PackedKV.Pkv)
  {
    pkv := getPkv(this_.store, this_.bucketIdx);
  }

  method PageBucketsFromPKVBuckets(pkvBuckets:seq<PackedKV.Pkv>)
    returns (pageBuckets:seq<PageBucket>)
    ensures true
  {
    var numBuckets:uint64 := |pkvBuckets| as uint64;
    var bucketOffsetsArray := new uint32[numBuckets+1];

    // Populate bucketOffsetsArray; compute the lengths of the other arrays
    var numKvPairs:uint64 := 0;
    var numDataBytes:uint64 := 0;
    var bucketIdx := 0;
    while bucketIdx < numBuckets {
      bucketOffsetsArray[bucketIdx] := numKvPairs as uint32;

      var pkvBucket := pkvBuckets[bucketIdx];
      var kvIdx := 0;
      var kvLen := PackedKV.NumKVPairs(pkvBucket);
      numKvPairs := numKvPairs + kvLen;
      while kvIdx < kvLen {
        var keySeq := PackedKV.GetKey(pkvBucket, kvIdx);
        var keyLen := |keySeq| as uint64;
        var valueSeq := PackedKV.GetMessageBytes(pkvBucket, kvIdx);
        var valueLen := |valueSeq| as uint64;
        numDataBytes := numDataBytes + keyLen + valueLen;
        kvIdx := kvIdx + 1;
      }
      bucketIdx := bucketIdx + 1;
    }
    bucketOffsetsArray[bucketIdx] := numKvPairs as uint32;
    var numPages := (numDataBytes + PageSize() - 1) / PageSize();
    var allocSize := numPages * PageSize();
    assert numDataBytes <= allocSize;
    
    // Allocate the arrays
    var keyOffsetsArray := new uint32[numKvPairs+1];
    var valueOffsetsArray := new uint32[numKvPairs+1];
    var dataArray := new byte[allocSize];

    // "write pointers"
    var dataOffset:uint64 := 0;
    var keyOffsetIdx:uint64 := 0;
    var valueOffsetIdx:uint64 := 0;

    // Populate keyOffsetsArray, key side of dataArray
    bucketIdx := 0;
    while bucketIdx < numBuckets {
      var pkvBucket := pkvBuckets[bucketIdx];
      var kvIdx := 0;
      var kvLen := PackedKV.NumKVPairs(pkvBucket);
      while kvIdx < kvLen {
        keyOffsetsArray[keyOffsetIdx] := dataOffset as uint32;
        var keySeq := PackedKV.GetKey(pkvBucket, kvIdx);
        var keyLen := |keySeq| as uint64;
        CopySeqIntoArray(keySeq, 0, dataArray, dataOffset, keyLen);
        dataOffset := dataOffset + keyLen;
        keyOffsetIdx := keyOffsetIdx + 1;
        kvIdx := kvIdx + 1;
      }
      bucketIdx := bucketIdx + 1;
    }
    keyOffsetsArray[keyOffsetIdx] := dataOffset as uint32;

    // Populate valueOffsetsArray, value side of dataArray
    bucketIdx := 0;
    while bucketIdx < numBuckets {
      var pkvBucket := pkvBuckets[bucketIdx];
      var kvIdx := 0;
      var kvLen := PackedKV.NumKVPairs(pkvBucket);
      while kvIdx < kvLen {
        valueOffsetsArray[valueOffsetIdx] := dataOffset as uint32;
        var valueSeq := PackedKV.GetMessageBytes(pkvBucket, kvIdx);
        var valueLen := |valueSeq| as uint64;
        CopySeqIntoArray(valueSeq, 0, dataArray, dataOffset, valueLen);
        dataOffset := dataOffset + valueLen;
        valueOffsetIdx := valueOffsetIdx + 1;
        kvIdx := kvIdx + 1;
      }
      bucketIdx := bucketIdx + 1;
    }
    valueOffsetsArray[valueOffsetIdx] := dataOffset as uint32;

    // Break dataArray into the pages in pagesArray
    var dataLen := dataOffset;
    var pagesArray := new seq<byte>[numPages];
    dataOffset := 0;
    var pageOffset:uint64 := 0;
    while dataOffset < dataLen
      invariant dataOffset == pageOffset * PageSize()
    {
      var len := PageSize();
      pagesArray[pageOffset] := dataArray[dataOffset..dataOffset+len];
      pageOffset := pageOffset + 1;
      dataOffset := dataOffset + len;
    }

    var store := PageBucketStore(bucketOffsetsArray[..], keyOffsetsArray[..], valueOffsetsArray[..], pagesArray[..]);

    var pageBucketsArray := new PageBucket[numBuckets];
    var i:uint64 := 0;
    while i < numBuckets {
      pageBucketsArray[i] := PageBucket(store, i);
      i := i + 1;
    }
    pageBuckets := pageBucketsArray[..];
  }
} // module PageBucketImpl
