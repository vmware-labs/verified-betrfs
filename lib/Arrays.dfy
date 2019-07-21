module Arrays {
  method Insert<T>(arr: array<T>, length: int, element: T, pos: int)
    requires 0 <= length < arr.Length
    requires 0 <= pos <= length
    ensures arr[..] == old(arr[..pos]) + [element] + old(arr[pos..length]) + old(arr[length+1..])
    modifies arr
  {
    ghost var oldarr := arr[..];

    var curelement := arr[pos];
    arr[pos] := element;

    var i := pos+1;
    while i <= length
      invariant 0 <= i <= length+1
      invariant arr == old(arr)
      invariant forall j :: 0 <= j < pos ==> arr[j] == oldarr[j]
      invariant arr[pos] == element
      invariant forall j :: pos < j < i ==> arr[j] == oldarr[j-1]
      invariant forall j :: i <= j < arr.Length ==> arr[j] == oldarr[j]
      invariant curelement == oldarr[i-1];
    {
      var tmp := arr[i];
      arr[i] := curelement;
      curelement := tmp;
      i := i + 1;
    }
  }

  method Memcpy<T>(dest: array<T>, destoffset: int, src: seq<T>)
    requires 0 <= destoffset <= dest.Length - |src|
    ensures dest[..] == old(dest[..destoffset]) + src + old(dest[destoffset + |src|..])
    modifies dest
  {
    var i := 0;
    while i < |src|
      invariant 0 <= i <= |src|
      invariant forall j :: 0              <= j < destoffset      ==> dest[j] == old(dest[j])
      invariant forall j :: destoffset     <= j < destoffset + i  ==> dest[j] == src[j-destoffset]
      invariant forall j :: destoffset + i <= j < dest.Length     ==> dest[j] == old(dest[j])
    {
      dest[destoffset + i] := src[i];
      i := i + 1;
    }
  }
}
