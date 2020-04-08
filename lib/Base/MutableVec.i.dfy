include "../Lang/NativeTypes.s.dfy"
include "Option.s.dfy"
include "sequences.i.dfy"

module MutableVec {
  import opened NativeTypes
  import opened Options
  import opened Sequences

  class Vec<V(==)> {
    var Array: array<Option<V>>;
    var Length: uint64;

    ghost var Contents: seq<V>;

    predicate Inv()
      reads this
      reads Array
    {
      && 0 < Array.Length < 0x10000000000000000
      && 0 <= (Length as int) < 0x10000000000000000
      && Length as int <= Array.Length 

      && (forall i :: 0 <= i < (Length as int) ==> Array[i].Some?)
      && (forall i :: (Length as int) <= i < Array.Length ==> Array[i].None?)

      && |Contents| == (Length as int)
      && (forall i :: 0 <= i < (Length as int) ==> Array[i].Some? && Array[i].value == Contents[i])
    }

    constructor (size: uint64)
      requires 0 < size
      ensures Inv()
      ensures Contents == []
    {
      Length := 0;
      Array := new [size] (_ => None);
      Contents := [];
    }

    method realloc()
      requires Inv()
      requires Array.Length < (0x10000000000000000 / 2)
      ensures Inv()
      ensures Contents == old(Contents)
      ensures Length == old(Length)
      ensures Length as int < Array.Length
      ensures fresh(this.Array)
      modifies this
    {
      var targetSize := Array.Length * 2;
      var newArray := new [targetSize] (_ => None);

      var k := 0;
      while k < Length
        invariant Inv()
        invariant (k as int) <= Array.Length <= newArray.Length
        invariant forall i :: 0 <= i < k ==> newArray[i] == Array[i]
        invariant forall i :: (Length as int) <= i < newArray.Length ==> newArray[i].None?
        invariant Contents == old(Contents);
        invariant Length == old(Length)
      {
        newArray[k] := Array[k];
        k := k + 1;
      }

      Array := newArray;
    }

    method insert(value: V)
      requires Inv()
      requires Array.Length < (0x10000000000000000 / 2)
      ensures Inv()
      ensures Contents == old(Contents) + [value]
      ensures Length == old(Length) + 1
      modifies this.Array
      modifies this
    {
      if Length as int == Array.Length {
        realloc();
      }
      Contents := Contents + [value];
      Array[Length] := Some(value);
      Length := Length + 1;
    }

    // Removes the element at index and moves the last element to index.
    method removeSwap(index: uint64) returns (removed: V)
      requires Inv()
      requires 0 <= (index as int) < (Length as int)
      ensures Inv()
      ensures (
        if (index as int) < ((old(Length) as int) - 1) then
          Contents == old(Contents)[..(index as int)] + [old(Contents)[|old(Contents)| - 1]] + old(Contents)[(index as int)+1..|old(Contents)|-1]
        else
          Contents == old(Contents)[..(index as int)])
      ensures Length == old(Length) - 1
      ensures removed == old(Contents)[index]
      modifies this.Array
      modifies this
    {
      removed := Array[index].value;

      Array[index] := Array[Length - 1];
      Array[Length - 1] := None;
      Length := Length - 1;

      if (index as int) < (old(Length) as int) - 1 {
        Contents := old(Contents)[..index] + [old(Contents)[|old(Contents)| - 1]] + old(Contents)[(index as int)+1..|old(Contents)|-1];
      } else {
        Contents := old(Contents)[..(index as int)];
      }
    }

    method pop() returns (removed: V)
      requires Inv()
      requires 1 < Length
      ensures Inv()
      ensures Contents == old(Contents)[..|old(Contents)|-1]
      ensures Length == old(Length) - 1
      ensures removed == old(Contents)[|old(Contents)|-1]
      modifies this.Array
      modifies this
    {
      removed := Array[Length - 1].value;

      Array[Length - 1] := None;
      Length := Length - 1;

      Contents := old(Contents)[..|old(Contents)|-1];
    }

    function method get(index: uint64): (result: V)
      requires Inv()
      requires 0 <= (index as int) < (Length as int)
      ensures Inv()
      ensures result == Contents[index]
      reads this
      reads this.Array
    {
      Array[index].value
    }

    method toSeq() returns (result: seq<V>)
      requires Inv()
      ensures Inv()
      ensures Contents == old(Contents)
      ensures Length == old(Length)
      ensures result == Contents
    {
      assert forall i :: 0 <= i < Length ==> Array[i].Some?;
      var contents: array<V> := new [Length] (
        (i: int) requires Inv() requires 0 <= i < (Length as int) reads this.Array, this => get(i as uint64));
      result := contents[..];
    }
  }
}
