#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

verus!{

#[is_variant]
pub enum Option<T>{
    None,
    Some(T)
}
}