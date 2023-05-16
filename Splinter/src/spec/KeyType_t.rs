#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus!{

pub struct Key(pub nat); // TODO: this is a placeholder for the Key type

#[is_variant]
pub enum Element {
    Max,
    Elem{e: nat}, // TODO: place holder
}

pub open spec fn to_key(elem: Element) -> Key
    recommends elem.is_Elem()
{
    Key(elem.get_Elem_e())
}

pub open spec fn to_element(key: Key) -> Element
{
    Element::Elem{e: key.0}
}

impl Key {
    // TODO: place holder for seq comparison of bytes
    pub open spec fn lte(a: Key, b: Key) -> bool
    {
        a.0 <= b.0
    }

    pub open spec fn lt(a: Key, b: Key) -> bool
    {
        &&& Key::lte(a, b) 
        &&& a != b
    }
}

impl Element {
    pub open spec fn lte(a: Element, b: Element) -> bool 
    {
        ||| b.is_Max()
        ||| (a.is_Elem() && b.is_Elem() && Key::lte(to_key(a), to_key(b)))
    }

    pub open spec fn lt(a: Element, b: Element) -> bool 
    {
        &&& Element::lte(a, b) 
        &&& a != b
    }

    pub open spec fn min_elem() -> Element
    {
        Element::Elem{e: 0} // place holder 
    }

    pub open spec fn is_strictly_sorted(run: Seq<Element>) -> bool
    {
        forall |i: int, j: int| 0 <= i < j < run.len() ==> Element::lt(run[i], run[j])
    }

    pub open spec fn largest_lte(run: Seq<Element>, needle: Element) -> int
        decreases run.len()
    {
        if run.len() == 0 || Element::lt(needle, run[0]) {
            -1
        } else {
            1 + Element::largest_lte(run.subrange(1, run.len() as int), needle)
        }
    }
} // end impl KeyType
}// end verus!
