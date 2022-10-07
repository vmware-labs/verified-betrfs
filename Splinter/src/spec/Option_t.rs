#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

verus!{

pub enum Option<T>{
    None,
    Some(T)
}
}