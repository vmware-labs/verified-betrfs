include "../lib/DataStructures/MutableMapModel.i.dfy"
include "LinearSequence.s.dfy"

// module LinearMutableMap {
  import opened MutableMapModel
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import opened Sets
  import opened SetBijectivity

  // import opened LinearSequence

  linear datatype FixedSizeHashMap<V> = FixedSizeHashMap(
    storage: lseq<Item<V>>,
    count: uint64,
    ghost contents: map<uint64, Option<V>>)

  protected static function ModelI<V>(self: FixedSizeHashMap<V>): (model: FixedSizeLinearHashMap<V>)
  ensures model.contents == self.contents
  {
    FixedSizeLinearHashMap(
      lseqs(self.storage),
      self.count,
      self.contents)
  }

  protected predicate Inv()
  requires WF()
  reads this, this.Repr
  {
    && FixedSizeInv(ModelI(this))
  }

// } // module
