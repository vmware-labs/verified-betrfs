# Linear type systems: related work and alternative designs

This document discusses the design of the linear type system in depth by
comparing to related work and presenting alternative approaches.

Key questions:
1. For a given variable `x` in a program, how does the type checker know whether `x`
should be treated linearly (duplication/discarding of `x` disallowed)
or nonlinearly (duplication/discarding of `x` allowed)?
2. For linear `xl` and nonlinear `xn`, is the assignment `xl := xn` allowed?
In other words, can nonlinear variables flow into linear variables?
3. What mechanism exists, if any, for temporarily viewing
mutable linear variables as immutable nonlinear variables?

For example, linear Dafny's answers to these questions are:
1. Each linear variable declaration is annotated with `linear`,
and each nonlinear variable declaration is annotated with `shared` or an empty annotation.
2. No, `xl := xn` is not allowed; linear and nonlinear variables are strictly segregated.
3. `linear` variables may be borrowed as nonlinear `shared` variables,
which are segregated from ordinary nonlinear variables.
Typing rules enforce a lexical scope restriction on `shared` variables where borrowing occurs.

## Girard's linear logic

In 1987, Girard introduced a linear logic that could directly express
consumption and production of limited resources
(see Wadler's "A Taste of Linear Logic" from 1993 for an introduction).
For example, Girard's `-o` operator is similar to classical logic's implication operator `==>`,
but `A -o B` consumes `A` when producing `B`, so that you no longer have `A` after using `A -o B`.
By contrast, `A ==> B` produces `B` without consuming `A`;
classical logic expresses that if you know some fact `A`,
you can use that knowledge infinitely many times and never lose it.
Girard's logic uses a special operator, `!`, to represent an infinite supply of a resource:
`A` by itself can only be used once, but `!A` can be duplicated an unbounded number of times, yielding
an unbounded number of `A`s.

For example, if you start with four resources, `dollar`, `dollar`, `dollar` and `(dollar -o banana)`,
you can use `dollar` and `(dollar -o banana)` to buy just one banana,
so that you end up with `dollar`, `dollar`, and `banana`.
If you start with `dollar`, `dollar`, `dollar` and `!(dollar -o banana)`,
you can buy multiple bananas, so that you may end up with
`banana`, `banana`, `banana` and `!(dollar -o banana)`.
If you start with `!dollar` and `!(dollar -o banana)`,
you can obtain as many bananas as you want.

Answers to key questions (following Wadler's "A Taste of Linear Logic" presentation of Girard's work):
1. `x` may be declared as a function parameter or as a binding for `!A`:
  * a function `lambda x:A. e` has type `A -o B`, assuming `e` has type `B`, and `x` is linear
  * if an expression `e` has type `!A`, then `let !x = e in e'`
  (written as `case e of !x -> e'` in Wadler's presentation)
  introduces `x:A` nonlinearly in `e'`
2. Yes, nonlinear variables can flow into linear variables: if nonlinear `xn` has type `A`,
then `xn` can be passed as an argument to a `A -o B` function.
3. No borrowing

## Wadler's "Linear Types Can Change the World"

Wadler's 1990 paper introduced a type system inspired by Girard's linear logic.
Rather than using Girard's `!` operator, though, Wadler's approach
contained both linear and nonlinear versions of various operators.
For example, for implication (function types), Wadler's system
contained both a linear `A -o B` and a nonlinear `A -> B`,
where `A -> B` is analogous to Girard's `!(A -o B)`.

In Wadler's system, every type is either linear or nonlinear.
For example, `A -o B` is linear and `A -> B` is nonlinear.
Values with linear type must be used exactly once, whereas values with nonlinear
type may be duplicated and discarded.
By strictly segregating linear and nonlinear types,
Wadler's approach gives valuable information to a compiler and run-time system:
if a variable `x` has linear type, then `x` contains the only reference to a value (no aliasing),
and it is safe to modify the value in place.

Wadler's 1990 type system did not have generics/polymorphism,
but any type system that extends Wadler's approach with polymorphism must answer the following question:
if a function is polymorphic over some type `A`, should `A` be considered linear or nonlinear?
Systems that followed Wadler's approach often used a kind system to answer this question,
so that a type variable `A` can be declared with kind `linear` if it is intended to be linear
and kind `nonlinear` if it is intended to be nonlinear (for example, see the description of Cogent below).
It is also possible to support polymorphism over the linearity itself,
with type or kind variables that can be instantiated with `linear` or `nonlinear`
(see Ahmed, Fluet, and Morrisett, "A Step-Indexed Model of Substructural State", 2005,
or Walker, "Substructural Type Systems", 2005).

Wadler's 1990 type system also introduced the idea of borrowing read-only access to a linear variable.
To understand how linear Dafny builds on (and differs from) Wadler's idea,
here is linear Dafny's rule for typing `u1 var x := e1; e2 : u2` from [TypingRules.md](TypingRules.md),
specialized to `u1 = ordinary` and omitting treatment of ghost variables and mutable borrowing:

```
O       ; S, Bs ; L1         |-           e1     : u1
O, {x1} ; S     ;     Bs, L2 |-               e2 : u2
-----------------------------------------------------
O       ; S     ; L1, Bs, L2 |- var x1 := e1; e2 : u2
```

Here is what Wadler's original rule would look like written in the notation of [TypingRules.md](TypingRules.md):

```
For each xs in Bs, x1's type is "safe" for xs's type
O, Bs   ; L1         |-                e1     : u1
O, {x1} ;     Bs, L2 |-                    e2 : u2
--------------------------------------------------
O       ; L1, Bs, L2 |- var!(Bs) x1 := e1; e2 : u2
```

The idea behind the two rules is very similar: the variables `Bs` are borrowed nonlinearly in `e1`
and then become linear again in `e2`.
(Wadler's syntax has `Bs` explicitly in the `var` declaration, but it's easy and useful for linear Dafny to infer `Bs`.)
Linear Dafny treats borrowed variables cautiously,
using lexical scoping rules to make sure that borrowed variables don't escape from `e1`.
Linear Dafny's scoping enforcement mechanism is simple and crude
(compared with, say, Rust, which has more sophisticated scoping enforcement):
it puts *all* read-only borrowed variables into the set `S`, and *no* variables in `S` can be returned from `e1` through `x1`.
Ordinary variables in `O`, on the other hand, can be returned in `x1`.
In other words, the segregation between `S` and `O` blocks shared variables and allows ordinary to pass.

By contrast, Wadler's proposal is more aggressive: it borrows directly into `O`.
This is convenient in some ways; there's no distinction between `var` and `shared var` for the programmer to worry about.
But it comes with an unusual restriction on the type of `x1`:
the type of `x1` cannot be a data structure with nonlinear field of an type that could contain any data read from the borrowed variables,
nor can `x1` contain a function type.
It is not obvious how to extend this restriction to more complex type systems.
For example, what if `x1`'s type is abstract, so the type checker can't see whether it is a datatype with nonlinear fields?
Because of these issues, later systems like Rust, Cogent, and linear Dafny have all used
other approaches to prevent borrowed variables from escaping.

Answers to key questions:
1. If `x` has type `t`, then `x` is linear if `t` is linear and `x` is nonlinear if `t` is nonlinear.
2. No, `xl := xn` is not allowed; linear and nonlinear variables are strictly segregated.
3. Yes, linear variables may be borrowed read-only, but only if the types of the variables obviously disallow leaking the borrowed variables.

## Linear Haskell

Linear Haskell (POPL 2018) follows Girard's approach more than Wadler's 1990 approach.
It includes both an `A -o B` type and an `A -> B` type.
(The `A -> B` type is like Girard's `!A -o B`, although linear Haskell's datatype rules
differ slightly from Girard's, allowing `(A, B) -> A` to extract just the first item of a pair,
for example, whereas `!(A, B) -o A` is deliberately not provable in Girard's logic.)
If `e` has type `B`, then a function `lambda linear x:A. e` has type `A -o B`, using `x` linearly,
and a function `lambda nonlinear x:A. e` has type `A -> B`, using `x` nonlinearly.
In contrast to Wadler's 1990 approach, the type of `A` has no influence over `x`'s linearity.

A function of type `A -o B` must use its argument `x:A` linearly.
As in Girard's approach, but in contrast to Wadler's 1990 approach,
callers of a `A -o B` may pass in any argument of type `A`, linear or nonlinear.
There is no a priori guarantee that a linear variable `x` holds unaliased data.
How, then, can linear Haskell safely allow in-place updates to `x`?
Linear Haskell's answer, following section 5.3 of Wadler's 1993 "A Taste of Linear Logic",
is that if a type T supports in-place update,
then no values of type T are ever placed into nonlinear variables.
For example, the constructor for mutable arrays, of type `MArray a`,
puts the newly allocated array into a linear variable,
and there's no way to assign a linear variable to a nonlinear variable.
Thus, any linear variable `x` of type `MArray a` must contain the only reference to the array.

This approach has advantages and disadvantages.
By allowing nonlinear variables to flow into linear variables,
it allows more code reuse across linear and nonlinear code.
There's no need to have separate linear and nonlinear list types,
for example: you can declare a linear list type and then use that type
for both linear lists and nonlinear lists.
On the other hand, such a list type cannot support in-place updates,
because a linear `x` with a list in it could be an alias to a nonlinear list.
Linear datatypes in linear Dafny, by contrast, do support in-place updates.
Furthermore, linear Dafny uses standard Dafny's `seq` type both nonlinearly, without in-place updates,
and linearly, with in-place updates.

Haskell pushes even further with linear/nonlinear code reuse by supporting
multiplicity polymorphism, where functions can be polymorphic over linearity.
For example, a single `map` function for lists can be declared to work both
for functions of type `A -o B` and `A -> B`.

Answers to key questions:
1. `x` may be declared as a linear function parameter (for `A -o B` function types)
or as a nonlinear function parameter (for `A -> B` function types).
2. Yes, nonlinear variables can flow into linear variables: if nonlinear `xn` has type `A`,
then `xn` can be passed as an argument to a `A -o B` function.
3. The POPL 2018 paper proposes an extension to linear Haskell for borrowing as future work.

## CIVL and linear maps

Linear Dafny took its `linear x:t` syntax from CIVL's linear variables
("Automated and modular refinement reasoning for concurrent programs", CAV 2015),
which in turn grew out of Lahiri, Qadeer, and Walker's "Linear Maps" (PLPV 2011).
As in Linear Haskell, CIVL associates linearity with variable declarations
rather than with types.
As in linear Dafny, nonlinear variables cannot flow into linear variables.
CIVL lacks borrowing, so there are no `shared` variables.

1. Each linear variable declaration is annotated with `linear`,
and nonlinear variable declarations have no annotation.
2. No, `xl := xn` is not allowed; linear and nonlinear variables are strictly segregated.
3. No mechanism for borrowing.

## Cogent

The Cogent language ("Cogent: Certified Compilation for a Functional Systems Language", 2016)
uses linear types for systems programming,
avoiding the need for garbage collection or reference counting.
In Cogent, unboxed values (primitive types and flat records, for example) may be nonlinear
but references are linear.

Cogent follows Wadler's 1990 approach of using variable types to determine variable linearity,
organizing the types into *kinds* that represent different levels of linearity.
These kinds aren't named "linear" and "nonlinear", but instead are written as sets
of permissions: `D` for discardable, `S` for duplicable, and `E` for escapes-from-borrowing.
The most common kinds correspond to linear Dafny's ordinary, shared, and linear variables:

| Cogent kind  | linear Dafny   |
|--------------|----------------|
| `{D, S, E}`  | ordinary       |
| `{D, S}`     | shared         |
| `{E}`        | linear         |

Other combinations of permissions are less familiar,
but some correspond to affine/relevant types (see Walker, "Substructural Type Systems", 2005).
In addition, a mutably borrowed variable in linear Dafny might be thought of as having Cogent kind `{}`,
although Cogent doesn't directly use mutable borrowing:

| Cogent kind  | analogous to     |
|--------------|------------------|
| `{D, E}`     | affine           |
| `{S, E}`     | relevant         |
| `{D}`        | affine shared    |
| `{S}`        | relevant shared  |
| `{}`         | mutable borrowed |

Like Wadler's 1990 approach, Cogent uses an explicit `!` variable binding syntax to borrow a variable.
However, Cogent does not use Wadler's "safe for" type rule to prevent borrowed variables from escaping.
Instead, Cogent's approach is like that of Rust and linear Dafny:
- When borrowing a linear variable `x` of type `T`, the borrowed variable appears
with type `bang(T)` in the borrowed scope, where `bang` replaces linear (`{E}`) with shared (`{D, S}`).
- Anything returned from a borrowing must be of a kind that includes `{E}`,
which forbids returning the shared (`{D, S}`) data.

In many linear type systems, it is difficult to read or write a single linear field of a datatype:
reading the field would duplicate the field's linear data, which is not allowed,
and overwriting the field would discard the field's linear data, which is also not allowed.
Some systems allow swapping the field's linear value for another linear value, preserving linearity.
Following Rust, linear Dafny allows mutable borrowing of a linear field.
Cogent, on the other hand, allows "taking" a value from a linear field of a record,
which changes the type of the record to indicate that the field's value was taken and
is therefore no longer available.
A program can put a value back into the field to restore the record's type and make the
field available again.
Linear Dafny does not include this take/put feature in the core language,
but uses it in some libraries, such as arrays.

Answers to key questions:

1. For a variable `x`, the type checker uses the type of `x` to determine `x`'s linearity.
Specifically, the type's kind specifies the linearity.
2. Cogent prohibits assigning shared (`{D, S}`) variables to linear ({`E`}) variables.
Compared to Wadler's 1990 approach, linear Dafny, and Linear Haskell,
Cogent makes very sparing use of nonlinear nonshared types (kind `{D, S, E}`).
This avoids the need for garbage collection or reference counting.
In particular, reference types are treated linearly (`{E}`) or temporarily shared (`{D, S}`), not `{D, S, E}`.
Because of this, the question of whether `{D, S, E}` variables are assignable to `{E}` variables is moot
and has no impact on performing in-place updates on references.
3. Cogent uses an explicit `!` syntax to introduce borrowing.
The borrowed variables' types are tagged as shared (`{D, S}`)
so that the shared variables can't escape the scope of the borrowing.

## Rust

Rust is a C-like language with a sophisticated type system for linearity and borrowing,
which allows Rust to be both low-level and type-safe, without requiring garbage collection
or reference counting.

Answers to key questions:

1. Rust uses a variable's type to determine the variable's linearity.
2. Rust prohibits assigning duplicable immutable variables to linear mutable variables.
3. Rust has a sophisticated borrowing system to temporarily view
linear mutable variables as duplicable immutable variables.

### References vs. value types

Rust is primarily an imperative language that manipulates C-like pointer-based data structures.
This contrasts with Wadler's 1990 language, Linear Haskell, and Cogent,
which are functional languages (although Cogent distinguishes between unboxed value types
and reference types).
Dafny supports both functional programming based on value types (e.g. seq, datatypes)
and imperative programming based on heap objects (e.g. arrays, class objects).
However, in contrast to Rust, linear Dafny uses linearity and borrowing just for
the functional subset of Dafny, for which it tends to be easier to write proofs.

### Lifetime parameters

One limitation of shared variables in linear Dafny (and similar `{D, S}` variables in Cogent)
is that the type checker blocks all shared variables from escaping
the scope of a borrowing.
In some cases, this is more restrictive than necessary.
In the following example, the call `F(x, y)` is not allowed to assign
the return value to a shared variable `y'`:

```dafny
function method F(shared x: int, shared y: int): (shared y': int) {
    y
}
function method Consume(linear x: int, shared y: int): ()
function method G(linear x: int, shared y: int): () {
    shared var y' := F(x, y); // FAILS: borrowing x blocks the return of shared y'
    Consume(x, y')
}
```

Blocking `y'` is unfortunate in this example.
It's important to block `F(x, y)` from returning `x` as shared,
so that `x` cannot be simultaneously `linear` and `shared`,
but returning `y` as shared is perfectly safe.

Rust "lifetime parameters" can distinguish between varying lifetimes
of different borrowed variables.
If linear Dafny had Rust's lifetime parameters,
then the code above could be written as:

```dafny
function method F<a, b>(shared<a> x: int, shared<b> y: int): (shared<b> y': int) {
    y
}
function method Consume(linear x: int, shared y: int): ()
function method G(linear x: int, shared y: int): () {
    shared var y' := F(x, y); // ok to return y' because of its long lifetime
    Consume(x, y')
}
```

In this (hypothetical) code, `F`'s parameters `x` and `y` have explicitly
different lifetimes `a` and `b`, and the return value `y'` has the same lifetime as `y`,
namely `b`.
This tells `G` that `y'` outlives the borrowing of the linear `x`,
and therefore is safe to store in a local shared variable.

### Borrowing components of data structures

Linear Dafny's type system tracks borrowing of variables.
In some cases, it would be useful to separately borrow different components
of the data stored in a single variable:

```dafny
method M1(shared x: int, shared y: int)
method M2(linear inout x: int, shared y: int)
method M3(linear inout x: int, linear inout y: int)
method N(linear inout p: (linear int, linear int)) {
    M1(p.0, p.1); // supported (borrows all of p once, uses shared borrowed p twice)
    M2(inout p.0, p.1);       // not yet supported in linear Dafny: separately borrowing p.0 and p.1
    M3(inout p.0, inout p.1); // not yet supported in linear Dafny: separately borrowing p.0 and p.1
}
```

Rust's checker tracks borrowing of fine-grained "paths" through variables, like `p.0` and `p.1`,
rather than just coarsely tracking borrowing of entire variables,
and is therefore able to support examples like the code shown above.

### Non-lexical lifetimes

Linear Dafny tracks the scope of linear and shared variables
to ensure that if shared `s` borrows from linear `x`,
then `x` remains unavailable until `s` is out of scope.
The following code fails to satisfy this criterion,
and is rejected by linear Dafny's type checker:

```dafny
function method Borrow(shared s: int): (shared s': int)
function method Consume(i: int, linear x: int): ()
function method F(shared s1: int, shared s2: int): (i: int)

function method G(linear x: int): () {
    shared var s := Borrow(x);
    var i := F(s, s);
    Consume(i, x) // FAILS: s is still lexically in scope when x is consumed
}
```

Thus, the code must be rewritten to reduce the scope of `s`:

```dafny
function method G(linear x: int): () {
    var i := (
        shared var s := Borrow(x);
        F(s, s));
    Consume(i, x) // SUCCEEDS: s is not in scope when x is consumed
}
```

Rewriting the code like this is inconvenient.
After all, there's nothing inherently unsafe about the first version
of `G`, since it doesn't actually use `s` simultaneously with consuming `x`.
Therefore, newer versions of Rust support non-lexical lifetimes,
so that the checker tracks the actual usage of variables like `s`
rather than just their scope.
