include "NativeTypes.s.dfy"
//include "Marshalling/Native.s.dfy"
include "sequences.i.dfy"

module Arrays {
  import Seq = Sequences
  //import Native
  import opened NativeTypes
    
  method Insert<T>(arr: array<T>, length: uint64, element: T, pos: uint64)
    requires 0 <= length as int < arr.Length < Uint64UpperBound()
    requires 0 <= pos <= length
    ensures arr[..length+1] == Seq.insert(old(arr[..length]), element, pos as int)
    ensures arr[length+1..] == old(arr[length+1..])
    modifies arr
  {
    // Native.Arrays.CopyArrayIntoArray(arr, pos, arr, pos+1, length-pos);
    // arr[pos] := element;
    
    ghost var oldarr := arr[..];

    var curelement := arr[pos];
    arr[pos] := element;

    var i := pos+1;
    while i <= length
      invariant pos+1 <= i <= length+1
      invariant arr == old(arr)
      invariant forall j :: 0 <= j < pos ==> arr[j] == oldarr[j]
      invariant arr[pos] == element
      invariant forall j :: pos < j < i ==> arr[j] == oldarr[j-1]
      invariant forall j :: i as int <= j < arr.Length ==> arr[j] == oldarr[j]
      invariant curelement == oldarr[i-1];
    {
      var tmp := arr[i];
      arr[i] := curelement;
      curelement := tmp;
      i := i + 1;
    }
  }

  method replace1with2<T>(arr: array<T>, length: uint64, element1: T, element2: T, pos: uint64)
    requires 0 <= length as int < arr.Length < Uint64UpperBound()
    requires 0 <= pos < length
    ensures arr[..length+1] == Seq.replace1with2(old(arr[..length]), element1, element2, pos as int)
    ensures arr[length+1..] == old(arr[length+1..])
    modifies arr
  {
    Insert(arr, length, element2, pos+1);
    arr[pos] := element1;

    ghost var replaced := Seq.replace1with2(old(arr[..length]), element1, element2, pos as int);
    assert forall i :: 0 <= i < pos ==> arr[i] == replaced[i];
    assert arr[pos] == replaced[pos];
    assert arr[pos+1] == replaced[pos+1];
    assert forall i :: pos+2 <= i < length+1 ==> arr[i] == old(arr[i-1]);
  }
  
  method Memcpy<T>(dest: array<T>, destoffset: uint64, src: seq<T>)
    requires 0 <= destoffset as int <= dest.Length - |src|
    ensures dest[..] == old(dest[..destoffset]) + src + old(dest[destoffset as int + |src|..])
    modifies dest
  {
    var i := 0;
    while i < |src|
      invariant 0 <= i <= |src|
      invariant forall j :: 0                     <= j < destoffset             ==> dest[j] == old(dest[j])
      invariant forall j :: destoffset as int     <= j < destoffset as int + i  ==> dest[j] == src[j-destoffset as int]
      invariant forall j :: destoffset as int + i <= j < dest.Length            ==> dest[j] == old(dest[j])
    {
      dest[destoffset as int + i] := src[i];
      i := i + 1;
    }
  }
}
