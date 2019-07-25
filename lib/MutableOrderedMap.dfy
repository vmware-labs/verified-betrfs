include "NativeTypes.dfy"
include "Option.dfy"
include "sequences.dfy"
// include "Sets.dfy"
// include "SetBijectivity.dfy"

abstract module MutableOrderedMap {
  import opened Options
  import opened Sequences

  type K(==)
  type V(==)
  function method LessEquals(a: K, b: K): bool
  function method Equals(a: K, b: K): bool
  function method LessThan(a: K, b: K): bool {
    LessEquals(a, b) && !Equals(a, b)
  }

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

  predicate LeftSmallerThanRight(left: map<K, V>, right: map<K, V>)
  {
    && (forall l, r :: l in left && r in right ==> LessThan(l, r))
  }

  // lemma LeftSmallerThanRightTransitive(mapA: map<K, V>, mapB: map<K, V>, mapC: map<K, V>)
  //   requires LeftSmallerThanRight(mapA, mapB)
  //   requires LeftSmallerThanRight(mapB, mapC)
  //   ensures LeftSmallerThanRight(mapA, mapC)
  // {
  //   forall a, c | a in mapA && c in mapC
  //   ensures LessThan(a, c)
  //   {
  //   }
  // }

  lemma LeftSmallerThanRightImpliesDisjunctKeySets(left: map<K, V>, right: map<K, V>)
    requires LeftSmallerThanRight(left, right)
    ensures left.Keys !! right.Keys
  {
    if exists k :: k in left.Keys && k in right.Keys {
      var k :| k in left.Keys && k in right.Keys;
      assert exists k :: k in left.Keys && k in right.Keys && !LessThan(k, k);
      assert false;
    }
    assert left.Keys !! right.Keys;
  }

  function InterpretData(data: seq<(K, V)>): (result: map<K, V>)
    requires forall i, j :: 0 <= i < |data| && 0 <= j < |data| && data[i].0 == data[j].0 ==> i == j
    ensures forall i :: 0 <= i < |data| ==> data[i].0 in result && result[data[i].0] == data[i].1
  {
    if |data| == 0 then
      map[]
    else
      var (k, v) := Last(data);
      InterpretData(DropLast(data))[k := v]
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
          ==> LeftSmallerThanRight(ContentsOf(Children[c1]), ContentsOf(Children[c2])))
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
      requires LeftSmallerThanRight(ContentsOf(left), InterpretData([datum]))
      requires LeftSmallerThanRight(InterpretData([datum]), ContentsOf(right))
      requires LeftSmallerThanRight(ContentsOf(left), ContentsOf(right))
      ensures Inv()
    {
      var newData := [datum];
      var newChildren := [left, right];
      Data := new [1] (i requires 0 <= i < 1 => newData[i]);
      Children := new [2] (i requires 0 <= i < 2 => newChildren[i]);

      Repr := ReprOf(left) + ReprOf(right);

      new;

      assert forall c1, c2 :: 0 <= c1 < c2 < Children.Length
          ==> LeftSmallerThanRight(ContentsOf(Children[c1]), ContentsOf(Children[c2]));
      LeftSmallerThanRightImpliesDisjunctKeySets(ContentsOf(left), InterpretData([datum]));
      LeftSmallerThanRightImpliesDisjunctKeySets(InterpretData([datum]), ContentsOf(right));
      assert forall d, c :: 0 <= d < Data.Length && 0 <= c < Children.Length
          ==> Data[d].0 !in ContentsOf(Children[c]).Keys;
      assert forall k :: k in Contents ==> (
          || (exists c ::
              && 0 <= c < Children.Length
              && var cnt := ContentsOf(Children[c]);
              && k in cnt && cnt[k] == Contents[k])
          || (exists i :: 0 <= i < Data.Length && Data[i] == (k, Contents[k])));
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
