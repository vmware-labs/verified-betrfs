include "../Lang/NativeTypes.s.dfy"
include "SeqComparison.s.dfy"

module {:extern} NativeArrays {
  import opened NativeTypes
  import SeqComparison

  method {:extern "NativeArrays_Compile", "ByteSeqCmpByteSeq"} ByteSeqCmpByteSeq(s1: seq<byte>, s2: seq<byte>)
      returns (c : int32)
      ensures c < 0 ==> SeqComparison.lt(s1, s2)
      ensures c > 0 ==> SeqComparison.lt(s2, s1)
      ensures c == 0 ==> s1 == s2

  method {:extern "NativeArrays_Compile", "newArrayFill"} newArrayFill<T>(n: uint64, t: T) returns (ar: array<T>)
  ensures ar.Length == n as int
  ensures forall i | 0 <= i < n :: ar[i] == t
  ensures fresh(ar)

  method {:extern "NativeArrays_Compile", "newArrayClone"} newArrayClone<T>(ar: array<T>) returns (ar': array<T>)
  ensures ar[..] == ar'[..]
  ensures fresh(ar')

  method {:extern "NativeArrays_Compile", "CopySeqIntoArray"} CopySeqIntoArray<A>(src:seq<A>, srcIndex:uint64, dst:array<A>, dstIndex:uint64, len:uint64)
      requires (srcIndex) as int + (len as int) <= |src|;
      requires (dstIndex as int) + (len as int) <= dst.Length;
      modifies dst;
      ensures  forall i :: 0 <= i < dst.Length ==> dst[i] == (
                  if (dstIndex as int) <= i < (dstIndex as int) + (len as int)
                  then src[i - (dstIndex as int) + (srcIndex as int)]
                  else old(dst[..])[i]);
      ensures  forall i :: (srcIndex as int) <= i < (srcIndex as int) + (len as int) ==>
                  src[i] == dst[i - (srcIndex as int) + (dstIndex as int)];

  method {:extern "NativeArrays_Compile", "CopyArrayIntoDifferentArray"} CopyArrayIntoDifferentArray<A>(src:array<A>, srcIndex:uint64, dst:array<A>, dstIndex:uint64, len:uint64)
      requires (srcIndex) as int + (len as int) <= src.Length;
      requires (dstIndex as int) + (len as int) <= dst.Length;
      requires src != dst
      modifies dst;
      ensures  forall i :: 0 <= i < dst.Length ==> dst[i] == (
                  if (dstIndex as int) <= i < (dstIndex as int) + (len as int)
                  then old(src[i - (dstIndex as int) + (srcIndex as int)])
                  else old(dst[..])[i]);
      ensures  forall i :: (srcIndex as int) <= i < (srcIndex as int) + (len as int) ==>
                  old(src[i]) == dst[i - (srcIndex as int) + (dstIndex as int)];


}
