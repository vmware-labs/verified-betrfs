use builtin_macros::*;
use builtin::*;

use crate::spec::TotalKMMap_t::*;
use crate::abstract_system::MsgHistory_v::MsgHistory;

verus! {
pub type LSN = nat;

// TODO(jonh): Templating isn't helping, would
// like to define wf for StampedMap

/// A Stamped type is one which has the concept of a seq_end.
/// I guess the original naming was meant to refer to how
/// you "stamp" the end with an LSN? IDK.
pub struct Stamped<T> {
  pub value: T, 
  pub seq_end: LSN 
}

/// A TotalKMMap with a seq_end field.
pub type StampedMap = Stamped<TotalKMMap>;

pub open spec(checked) fn empty() -> StampedMap {
  Stamped{ value: TotalKMMap::empty(), seq_end: 0}
}

impl StampedMap {
  pub open spec(checked) fn ext_equal(self, other: StampedMap) -> bool {
    &&& self.value.0 =~= other.value.0
    &&& self.seq_end == other.seq_end
  }

  /// Returns a StampedMap formed by applying the operations in the given journal
  /// (aka Message History) to this StampedMap.
  pub open spec(checked) fn plus_history(self, history: MsgHistory) -> StampedMap
    recommends
      self.value.wf(),
      history.wf(),
      history.can_follow(self.seq_end),
  {
    history.apply_to_stamped_map(self)
  }

  // Proofs:
  pub proof fn ext_equal_is_equality()
    ensures forall |a: StampedMap, b: StampedMap|
      a.ext_equal(b) == (a == b)
  {
  }
}

}


fn main() {}
