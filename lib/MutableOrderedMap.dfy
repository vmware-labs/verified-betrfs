include "NativeTypes.dfy"
include "Option.dfy"
// include "sequences.dfy"
// include "Sets.dfy"
// include "SetBijectivity.dfy"

abstract module MutableOrderedMap {
  type K(==)
  type V(==)
  function method LessEquals(a: K, b: K): bool
  function method Equals(a: K, b: K): bool
  function method LessThan(a: K, b: K): bool {
    LessEquals(a, b) && !Equals(a, b)
  }

  import opened Options

  datatype TwoThreeNodeRef = Internal(internal: InternalTwoThreeNode) | Leaf(leaf: LeafTwoThreeNode)

  function NodeOf(ref: TwoThreeNodeRef): object
  {
    match ref {
      case Internal(node) => node
      case Leaf(node) => node
    }
  }

  function ReprOf(ref: TwoThreeNodeRef): set<object>
    reads NodeOf(ref)
  {
    match ref {
      case Internal(node) => { node } + node.Repr
      case Leaf(node) => { node }
    }
  }

  function ContentsOf(ref: TwoThreeNodeRef): map<K, V>
    reads NodeOf(ref)
  {
    match ref {
      case Internal(node) => node.Contents
      case Leaf(node) => node.Contents
    }
  }

  class InternalTwoThreeNode {
    var Data: array<(K, V)>;
    var Children: array<TwoThreeNodeRef>;

    ghost var Repr: set<object>;
    ghost var Contents: map<K, V>;

    predicate Inv()
      reads this
      reads this.Children
      reads set i | 0 <= i < this.Children.Length :: NodeOf(this.Children[i])
      reads this.Data
    {
      && 2 <= Children.Length <= 3
      && Repr == (ReprOf(Children[0]) + ReprOf(Children[1]) +
          if Children.Length == 3 then ReprOf(Children[2]) else {})
      && (forall c1, c2 :: 0 <= c1 < c2 < Children.Length
          ==> (forall l, r :: l in ContentsOf(Children[c1]) && r in ContentsOf(Children[c2]) ==> LessThan(l, r)))
      && (forall d, c :: 0 <= d < Data.Length && 0 <= c < Children.Length
          ==> Data[d].0 !in ContentsOf(Children[c]).Keys)
      && (forall k :: k in Contents ==> (
          || (exists c ::
              && 0 <= c < Children.Length
              && var cnt := ContentsOf(Children[c]);
              && k in cnt && cnt[k] == Contents[k])
          || (exists i :: 0 <= i < Data.Length && Data[i] == (k, Contents[k]))))
    }

    constructor (left: TwoThreeNodeRef, datum: (K, V), right: TwoThreeNodeRef)
      ensures Inv()
    {
      var newData := [datum];
      var newChildren := [left, right];
      Data := new [1] (i requires 0 <= i < 1 => newData[i]);
      Children := new [2] (i requires 0 <= i < 2 => newChildren[i]);

      Repr := ReprOf(left) + ReprOf(right);
    }
  }

  class LeafTwoThreeNode {
    var Data: array<(K, V)>;

    ghost var Contents: map<K, V>;

    constructor (data: array<(K, V)>)
    {
      Data := data;
    }
  }

  class TwoThreeTree {
    var Root: TwoThreeNodeRef;

    ghost var Contents: map<K, V>;
    ghost var Repr: set<object>;

    predicate Inv()
      reads this
      reads NodeOf(this.Root)
    {
      && Repr == ReprOf(Root)
    }

    constructor ()
      ensures Inv()
    {
      var emptyData: array<(K, V)> := new [0];
      var leafNode := new LeafTwoThreeNode(emptyData);
      Root := Leaf(leafNode);
      
      Contents := map[];

      new;

      Repr := ReprOf(Root);
    }
  }
}
