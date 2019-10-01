include "../NativeTypes.s.dfy"

module {:extern} Native {
  import opened NativeTypes

  // Leverage .NET's ability to perform copies faster than one element at a time
  class Arrays
  {
      static method{:axiom} newArrayFill<T>(n: uint64, t: T) returns (ar: array<T>)
      ensures ar.Length == n as int
      ensures forall i | 0 <= i < n :: ar[i] == t
      ensures fresh(ar)

      static method{:axiom} newArrayClone<T>(ar: array<T>) returns (ar': array<T>)
      ensures ar[..] == ar'[..]
      ensures fresh(ar')

      static method{:axiom} CopySeqIntoArray<A>(src:seq<A>, srcIndex:uint64, dst:array<A>, dstIndex:uint64, len:uint64)
          requires (srcIndex) as int + (len as int) <= |src|;
          requires (dstIndex as int) + (len as int) <= dst.Length;
          modifies dst;
          ensures  forall i :: 0 <= i < dst.Length ==> dst[i] == (
                      if (dstIndex as int) <= i < (dstIndex as int) + (len as int)
                      then src[i - (dstIndex as int) + (srcIndex as int)]
                      else old(dst[..])[i]);
          ensures  forall i :: (srcIndex as int) <= i < (srcIndex as int) + (len as int) ==>
                      src[i] == dst[i - (srcIndex as int) + (dstIndex as int)];

      /*static predicate lt(a: seq<byte>, b: seq<byte>)
      {
        if |a| == 0 && |b| == 0 then false
        else if |a| == 0 then true
        else if |b| == 0 then false
        else if a[0] < b[0] then true
        else if a[0] > b[0] then false
        else lt(a[1..], b[1..])
      }

      static method{:axiom} ByteSeqCmpByteSeq(s1: seq<byte>, i1: int32, l1: int32, s2: seq<byte>, i2: int32, l2: int32)
          returns (c : int32)
          requires 0 <= i1
          requires 0 <= i2
          requires 0 <= l1
          requires 0 <= l2
          requires i1 as int + l1 as int <= |s1|
          requires i2 as int + l2 as int <= |s2|
          ensures c < 0 ==> lt(s1[i1 .. i1 + l1], s2[i2 .. i2 + l2])
          ensures c > 0 ==> lt(s2[i2 .. i2 + l2], s1[i1 .. i1 + l1])
          ensures c == 0 ==> s1[i1 .. i1 + l1] == s2[i2 .. i2 + l2]*/

  }

  class BenchmarkingUtil {
    static method{:axiom} start()
    static method{:axiom} end()
  }
}

