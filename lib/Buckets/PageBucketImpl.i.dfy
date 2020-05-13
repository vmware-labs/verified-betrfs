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

  function method PageSize() : uint64 { 4096 }  // XXX move to bounds

  method minUint64(a:uint64, b:uint64) returns (result:uint64) {
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

  method stitchBytes(this_: PageBucketStore, offset:uint64, len:uint64)
    returns (stitched: seq<byte>)
  {
    var stitchedArray := new byte[len];
    var nextPage := offset / PageSize();
    var nextOffset := offset % PageSize();
    var nextLen := minUint64(PageSize() - nextOffset, len);
    var nextArrayOffset:uint64 := 0;
    var remainingLen := len;

    while (nextLen > 0) {
      CopySeqIntoArray(this_.pages[nextPage], nextOffset as uint64, stitchedArray, nextArrayOffset as uint64, nextLen as uint64);
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

  method getKeysSize(this_: PageBucket)
    returns (size:uint64)
  {
    var bucketOffsetStart := this_.store.bucketOffsets[this_.bucketIdx];
    var bucketOffsetEnd := this_.store.bucketOffsets[this_.bucketIdx+1];
    var keysStart := this_.store.keyOffsets[bucketOffsetStart] as uint64;
    var keysEnd := this_.store.keyOffsets[bucketOffsetEnd] as uint64;
    return keysEnd - keysStart;
  }

  method getValuesSize(this_: PageBucket)
    returns (size:uint64)
  {
    var bucketOffsetStart := this_.store.bucketOffsets[this_.bucketIdx];
    var bucketOffsetEnd := this_.store.bucketOffsets[this_.bucketIdx+1];
    var valuesStart := this_.store.valueOffsets[bucketOffsetStart] as uint64;
    var valuesEnd := this_.store.valueOffsets[bucketOffsetEnd] as uint64;
    return valuesEnd - valuesStart;
  }

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
    assume false; // XXX
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

    // Allocate the arrays
    var keyOffsetsArray := new uint32[numKvPairs+1];
    var valueOffsetsArray := new uint32[numKvPairs+1];
    var dataArray := new byte[numDataBytes];

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
    var numPages := (dataLen + PageSize() - 1) / PageSize();
    var pagesArray := new seq<byte>[numPages];
    dataOffset := 0;
    var pageOffset:uint64 := 0;
    while dataOffset < dataLen {
      var len := minUint64(PageSize(), dataLen - dataOffset);
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
