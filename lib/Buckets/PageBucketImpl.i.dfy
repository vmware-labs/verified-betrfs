include "../../PivotBetree/Bounds.i.dfy"
include "BucketModel.i.dfy"
include "PackedKV.i.dfy"

module PageBucketImpl {
  import opened NativeTypes
  import opened BucketModel
  import opened KeyType
  //import opened ValueType`Internal
  import opened ValueMessage
  import opened Options
  import opened NativeArrays
  import PackedKV
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
  {
    method stitchBytes(offset:uint64, len:uint64)
      returns (stitched: seq<byte>)
    {
      var stitchedArray := new byte[len];
      var nextPage := offset / PageSize();
      var nextOffset := offset % PageSize();
      var nextLen := minUint64(PageSize() - nextOffset, len);
      var nextArrayOffset:uint64 := 0;
      var remainingLen := len;

      while (nextLen > 0) {
        CopySeqIntoArray(pages[nextPage], nextOffset as uint64, stitchedArray, nextArrayOffset as uint64, nextLen as uint64);
        nextArrayOffset := nextArrayOffset + nextLen;
        remainingLen := remainingLen - nextLen;

        nextPage := nextPage + 1;
        nextOffset := 0;
        nextLen := minUint64(PageSize(), remainingLen);
      }
      return stitchedArray[..];
    }

    method getKey(bucketIndex:uint64, kvIndexInBucket:uint64)
      returns (key: Key)
    {
      var kvIndex := bucketOffsets[bucketIndex] as uint64 + kvIndexInBucket;
      var keyOffset := keyOffsets[kvIndex] as uint64;
      var keyLen := keyOffsets[kvIndex+1] as uint64 - keyOffset;
      key := stitchBytes(keyOffset, keyLen);
    }

    method getValue(bucketIndex:uint64, kvIndexInBucket:uint64)
      returns (value:seq<byte>)
    {
      var kvIndex := bucketOffsets[bucketIndex] as uint64 + kvIndexInBucket;
      var valueOffset := valueOffsets[kvIndex] as uint64;
      var valueLen := valueOffsets[kvIndex+1] as uint64 - valueOffset;
      value := stitchBytes(valueOffset, valueLen);
    }
  }

  datatype PageBucket = PageBucket(store:PageBucketStore, bucketIdx:uint64)
  {
    method GetNumPairs() returns (result:uint64) {
      result := store.bucketOffsets[bucketIdx + 1] as uint64
                - store.bucketOffsets[bucketIdx] as uint64;
    }

    method Query(key: Key) returns (msg: Option<Message>)
    {
      var lo: uint64 := 0;
      var hi: uint64 := GetNumPairs();
      while lo < hi
      {
        var mid: uint64 := (lo + hi) / 2;
        var midKey := store.getKey(bucketIdx, mid);
        var c := KeyspaceImpl.cmp(key, midKey);
        if c == 0 {
          var valueBytes := store.getValue(bucketIdx, mid);
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

    method GetKey(idx:uint64) returns (key:Key)
    {
      key := store.getKey(bucketIdx, idx);
    }

    method IsEmpty() returns (empty: bool)
    {
      var numPairs := GetNumPairs();
      empty := numPairs  == 0;
    }

    method ToPkv() returns (pkv: PackedKV.Pkv)
    {
      assume false; // XXX
    }
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
    }
    pageBuckets := pageBucketsArray[..];
  }

} // module PageBucketImpl
