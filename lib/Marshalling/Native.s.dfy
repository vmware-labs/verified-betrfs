include "../Lang/NativeTypes.s.dfy"

module {:extern} Native {
  import opened NativeTypes

  // Leverage .NET's ability to perform copies faster than one element at a time
  class Arrays
  {
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

      static method{:axiom} CopyArrayIntoArray<A>(src:array<A>, srcIndex:uint64, dst:array<A>, dstIndex:uint64, len:uint64)
          requires (srcIndex) as int + (len as int) <= src.Length;
          requires (dstIndex as int) + (len as int) <= dst.Length;
          modifies dst;
          ensures  forall i :: 0 <= i < dst.Length ==> dst[i] == (
                      if (dstIndex as int) <= i < (dstIndex as int) + (len as int)
                      then src[i - (dstIndex as int) + (srcIndex as int)]
                      else old(dst[..])[i]);
          ensures  forall i :: (srcIndex as int) <= i < (srcIndex as int) + (len as int) ==>
                      src[i] == dst[i - (srcIndex as int) + (dstIndex as int)];
  }
}
