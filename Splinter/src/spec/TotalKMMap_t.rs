// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin_macros::*;
use vstd::prelude::*;
use vstd::set_lib::*;

use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;

verus!{

/// A TotalKMMap wraps a regular verus map. Maps Keys to Messages.
/// We use this to represent our abstract map state.
#[verifier::ext_equal]
pub struct TotalKMMap(pub Map<Key, Message>);

pub open spec(checked) fn total_domain() -> Set<Key>
{
    Set::new(|k:Key| true)
}

impl TotalKMMap
{
    pub open spec(checked) fn empty() -> TotalKMMap
    // ensures wf()
    {
        // TODO(verus): Should not have to declare binder twice.
        TotalKMMap(Map::new(
            |k: Key| true,
            |k: Key| Message::empty(),
        ))
    }

    // pass through to Map :v/
    pub open spec(checked) fn spec_index(self, idx: Key) -> Message
    recommends
        self.wf(),
    {
        self.0[idx]
    }

    // pass through to Map :v/
    pub open spec(checked) fn insert(self, key: Key, value: Message) -> Self
    // ensures wf() if recommends wf()
    {
        TotalKMMap(self.0.insert(key, value))
    }

    // pass through to Map :v/
    pub open spec(checked) fn dom(self) -> Set<Key>
    // ensures forall?
    {
        self.0.dom()
    }

    pub open spec(checked) fn wf(self) -> bool
    {
        self.dom() == total_domain()
    }

    // TODO(jonh): these silly wrappers can probably go away now that we have =~=?
    pub open spec(checked) fn ext_equal(self, other: TotalKMMap) -> bool
    {
        self.0 =~= other.0
    }

    pub proof fn ext_equal_is_equality(self, other: TotalKMMap)
        requires
            self.ext_equal(other)
        ensures
            self == other
    {}

    pub proof fn insert_lemma(self)
    requires
        self.wf(),
    ensures
        forall |k: Key, v: Message| #![auto] self.insert(k, v).wf(),
    {
        assert forall |k: Key, v: Message| (#[trigger] self.insert(k, v)).wf() by {
            assert_sets_equal!(self.insert(k, v).dom(), total_domain());
        }
    }
}

}
