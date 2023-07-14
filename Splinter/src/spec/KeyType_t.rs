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

pub open spec(checked) fn to_key(elem: Element) -> Key
    recommends elem.is_Elem()
{
    Key(elem.get_Elem_e())
}

pub open spec(checked) fn to_element(key: Key) -> Element
{
    Element::Elem{e: key.0}
}

impl Key {
    // TODO: place holder for seq comparison of bytes
    pub open spec(checked) fn lte(a: Key, b: Key) -> bool
    {
        a.0 <= b.0
    }

    pub open spec(checked) fn lt(a: Key, b: Key) -> bool
    {
        &&& Key::lte(a, b) 
        &&& a != b
    }
}

impl Element {
    pub open spec(checked) fn lte(a: Element, b: Element) -> bool 
    {
        ||| b.is_Max()
        ||| (a.is_Elem() && b.is_Elem() && Key::lte(to_key(a), to_key(b)))
    }

    pub open spec(checked) fn lt(a: Element, b: Element) -> bool 
    {
        &&& Element::lte(a, b) 
        &&& a != b
    }

    pub proof fn lt_transitive(a: Element, b: Element, c: Element)
        requires Self::lt(a, b), Self::lt(b, c)
        ensures Self::lt(a, c)
    {
    }

    pub proof fn lt_transitive_forall()
        ensures forall |a: Element, b: Element, c: Element| 
            Self::lt(a, b) && Self::lt(b, c) ==> Self::lt(a, c)
    {
        assert forall |a: Element, b: Element, c: Element| Self::lt(a, b) && Self::lt(b, c) 
        implies Self::lt(a, c) by {
            Self::lt_transitive(a, b, c);
        }
    }

    pub proof fn lte_transitive(a: Element, b: Element, c: Element)
        requires Self::lte(a, b), Self::lte(b, c)
        ensures Self::lte(a, c)
    {
    }

    pub proof fn lte_transitive_forall()
        ensures forall |a: Element, b: Element, c: Element| 
            Self::lte(a, b) && Self::lte(b, c) ==> Self::lte(a, c)
    {
        assert forall |a: Element, b: Element, c: Element| Self::lte(a, b) && Self::lte(b, c) 
        implies Self::lte(a, c) by {
            Self::lte_transitive(a, b, c);
        }
    }

    pub open spec(checked) fn min_elem() -> Element
    {
        Element::Elem{e: 0} // place holder 
    }

    pub open spec(checked) fn is_sorted(run: Seq<Element>) -> bool
    {
        forall |i: int, j: int| 0 <= i <= j < run.len() ==> Element::lte(run[i], run[j])
    }

    pub open spec(checked) fn is_strictly_sorted(run: Seq<Element>) -> bool
    {
        forall |i: int, j: int| 0 <= i < j < run.len() ==> Element::lt(run[i], run[j])
    }

    pub proof fn strictly_sorted_implies_sorted(run: Seq<Element>)
        requires Self::is_strictly_sorted(run)
        ensures Self::is_sorted(run)
    {
        assert forall |i: int, j: int| 0 <= i <= j < run.len()
        implies Element::lte(run[i], run[j]) by {
            if i < j {
                assert(Element::lt(run[i], run[j]));
            }
        }
    }

    pub open spec(checked) fn largest_lte(run: Seq<Element>, needle: Element) -> int
        decreases run.len()
    {
        if run.len() == 0 || Element::lt(needle, run[0]) {
            -1
        } else {
            1 + Element::largest_lte(run.subrange(1, run.len() as int), needle)
        }
    }

    pub proof fn largest_lte_lemma(run: Seq<Element>, needle: Element, out: int)
        requires Self::is_sorted(run), out == Self::largest_lte(run, needle)
        ensures -1 <= out < run.len(),
            forall |i: int| #![auto] 0 <= i <= out ==> Self::lte(run[i], needle),
            forall |i: int| #![auto] out < i < run.len() ==> Self::lt(needle, run[i]),
            run.contains(needle) ==> 0 <= out && run[out] == needle
        decreases run.len()
    {
        Self::lte_transitive_forall();
        if run.len() == 0 {
        } else if Element::lt(needle, run[0]) {
            if run.contains(needle) {
                assert(Element::lte(run[0], run[run.index_of(needle)]));
                assert(false);
            }
        } else {
            let sub_run = run.subrange(1, run.len() as int);
            Self::largest_lte_lemma(sub_run, needle, out-1);

            assert forall |i:int| out < i < run.len()
            implies #[trigger] Self::lt(needle, run[i]) 
            by {
                assert(run[i] == sub_run[i-1]);
            }

            if run.contains(needle) && !sub_run.contains(needle) {
                let idx = run.index_of(needle);
                if idx != 0 {
                    assert(sub_run[idx-1] == run[idx]);
                    assert(false);
                }
                assert(idx == 0);
                assert(run[0] == needle);

                if run.len() == 1 {
                    assert(out == 0);
                } else {
                    assert(Element::lt(run[0], run[1]));
                    assert(sub_run[0] == run[1]);
                    assert(out == 0);
                }
            }
        }
    }
} // end impl KeyType
}// end verus!
