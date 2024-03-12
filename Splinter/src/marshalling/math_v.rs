// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;

verus! {

#[verifier(nonlinear)]
pub proof fn div_mul_order(a: int, b: int)
requires 0 < b
ensures (a/b) * b <= a
{
}

#[verifier(nonlinear)]
pub proof fn mul_le(a: int, b: int)
    requires 0<=a, 1<=b
    ensures a <= a*b
{
}

#[verifier(nonlinear)]
pub proof fn euclidean_div_truncates(x: int, y: int)
    requires 0<=x, 0<y
    ensures (x/y) * y <= x
{
}

#[verifier(nonlinear)]
pub proof fn mul_div_identity(x: int, y: int)
    requires 0!=y
    ensures (x*y)/y == x
{
}

#[verifier(nonlinear)]
pub proof fn pos_mul_preserves_order(x: int, y: int, m: int)
    requires 0<= x < y, 0 < m
    ensures x*m < y*m
{}

#[verifier(nonlinear)]
pub proof fn distribute_left(a: int, b: int, c: int)
    ensures (a+b)*c == a*c + b*c {}

#[verifier(nonlinear)]
pub proof fn mul_preserves_le(a: int, b: int, c: int)
    requires 0 <= a <= b, 0 <= c
    ensures a * c <= b * c
{ }

pub proof fn nat_mul_nat_is_nat(x: int, y: int)
    requires 0 <= x, 0 <= y
    ensures 0 <= x*y {}

pub proof fn lemma_seq_slice_slice<T>(s: Seq<T>, i: int, j: int, k: int, l: int)
    requires 0 <= i <= j <= s.len(),
        0 <= k <= l <= j-i
    ensures s.subrange(i,j).subrange(k,l) =~= s.subrange(i+k, i+l)
{
}

}
