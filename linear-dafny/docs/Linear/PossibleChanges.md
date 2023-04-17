# Alternatives and possible future extensions

This document discusses possible changes to the current design and implementation of linear Dafny.
The discussion is meant to be speculative and open ended.

Also see the ideas posted as [GitHub issues](https://github.com/secure-foundations/dafny/issues).

## Syntax

The keyword `unique` could be friendlier than `linear`.

## More built-in operations on linear abstract data types

The document [Library.md](Library.md) discusses functions on linear/shared sequences
as well as types `lseq` and `SwapLinear`.
Some of these functions or types could be built into the language.
For example, `|s|`, `s[i]`, and `s[i := v]` could easily apply to linear/shared `seq`,
meaning `SeqLength`, `SeqGet`, and `SeqUpdate`.
It might also be possible for the statement `s[i] := v` or `inout s[i] := v` to mean `SeqSet` for linear `seq`.

It should be possible to update ordinary fields of linear datatypes
with the `d.(x := v)` syntax; this is not yet supported,
although `inout d.x := y;` is supported.

Open questions:
- Is it better to add features directly to the language, or to use libraries (possibly with operator overloading)?
  - and should all functions be added to the language (`SeqAlloc`? `SeqFree`? `SeqUnleash?`)
  or just the functions that already have obvious language analogues, like `|s|` for `SeqLength`?
- Should `lseq` and `SwapLinear` be in the language, even though they are quite different from
existing built-in Dafny types?
- Should `seq` and `lseq` elements be usable as `inout` or `linear inout` arguments?
This would allow `Swap` to replace `LSeqSwap`, for example.

## Features from Rust

The [RelatedWork.md](RelatedWork.md) document mentions four features of Rust that could be useful for linear Dafny:
- Linear/shared treatment of Dafny's mutable types, like `array` and classes
- Lifetime parameters, which would generalize `shared`
- Separately borrowing different components of a data structure (paths)
- Non-lexical lifetimes

Each of these would be a substantial amount of work, but it's good to learn from Rust's experience.

## Borrowing for statements, not just expressions and calls

As discussed in [TypingRules.md](TypingRules.md),
linear Dafny supports borrowing within statements but not across statements.
The following is a simple proposal for supporting borrowing across statements
(simple, compared with Rust, for example).

The key observation is as follows:
in all the `O; L |- s : L'` rules from [TypingRules.md](TypingRules.md),
the L' variables flow to statements that execute strictly after s.
Therefore, s can safely borrow x from L before sending x back into L'.

There are two ways to express the ability to borrow variables from subsequent statements.
First, in `s1; s2`, the `s1` statements could borrow `Bs` from `s2`:

```
s1 does not assign to shared variables outside s1
G ; O ; S, Bs ; L0     |- s1 : L1
G ; O ; S     ; L1, Bs |- s2 : L2
-------------------------------------
G ; O ; S     ; L0, Bs |- s1; s2 : L2
```

Alternatively, there could be a simpler rule that applies to all statements:

```
s does not assign to shared variables outside s
G ; O ; S, Bs ; L     |- s : L'
-----------------------------------
G ; O ; S     ; L, Bs |- s : L', Bs
```

To infer `Bs` in either rule,
the type checker would track borrowing by changing each borrowed variable's
state from Available to Borrowed (as is currently done for expressions).
The checker would then try to revert Borrowed back to Available
at the soonest possible opportunity as it traverses the program's abstract syntax tree;
this corresponds to finding the smallest possible scope for borrowing.
The key constraint is the side condition
"s does not assign to shared variables outside s";
if this is not satisfied in a small scope,
the type checker must expand the scope until it finds a scope in which it is satisfied.
If no scope satisfies this, then the checker reports a type error.

For example, in the following code,
the checker would first consider the scope of the single statement `shared var s := M1(l);`.
This does not satisfy the side condition,
because `s` escapes the scope of the statement.
However, the next larger scope, `{shared var s := M1(l); M2(s);}`, does satisfy the side condition,
allowing type checking to succeed.

```dafny
method M1(linear l: LList<int>) returns(shared s: int)
method M2(shared s: int)
method M3(linear l: LList<int>)

method M(linear l: LList<int>) {
    {
        shared var s := M1(l);
        M2(s);
    }
    M3(l);
}
```

Note that the program has to put `shared var s := M1(l); M2(s);` inside a block for this to work,
as shown above.
(In the syntax of [TypingRules.md](TypingRules.md),
this corresponds a structure of `(s := M1(l); M2(s)); M3(l)`, with borrowing across `(s := M1(l); M2(s))`.)
The following (corresponding to `s := M1(l); (M2(s); M3(l))`) would not be allowed by the typing rules above:

```dafny
method M(linear l: LList<int>) {
    shared var s := M1(l);
    M2(s);
    M3(l); // not allowed: both s and l are available simultaneously here
}
```

Allowing this would require something like non-lexical lifetimes,
as supported by recent versions of Rust,
which would be nice but is beyond this proposal.

## More borrowing within expressions

### Borrowing in complex arguments

In some places, the current type checking implementation only allows borrowing
for variables that are direct arguments to functions.
This appears to be an unnecessary restriction,
and code like the following should be allowed according to [TypingRules.md](TypingRules.md):

```dafny
function method S1(shared i:int, shared j:int) : int

method S1_test(linear inout i:int)
{
    var _ := S1(i, (if true then i else i)); // borrowing in second argument is currently rejected
}
```

### Borrowing from neighboring arguments

Currently, for a linear `x` and an `F(ordinary, linear)`,
the expression `F(SeqLength(x), x)` is not allowed,
since `SeqLength(x)` can't borrow `x` when `x` is consumed as a neighboring argument to `F`.
Therefore, a programmer has to write this as:

```
var len := SeqLength(x); // borrowing x allowed here
F(len, x) // x consumed here
```

In `F(G(x), x)`, the variable `x` isn't truly consumed until it's inside `F`,
so in some sense `G(x)` temporally precedes `x`'s consumption,
and we could exploit this in the borrowing rules
to allow `F(SeqLength(x), x)`.
The rule wouldn't necessarily look pretty,
but it might be in the spirit of something like:

```
f : (u1 io1, u2 io2) -> uf
e1 is a function call
G ; O ; S, {x2} ; M1     ; L1       |-   e1      : u1 io1
G ; O ; S       ;     {} ;     {x2} |-       x2  : u2 io2
---------------------------------------------------------
G ; O ; S       ; M1     ; L1, {x2} |- f(e1, x2) : uf
```

This is essentially like checking "`var x1 := e1; f(x1, x2)`".
An implementation could run three phases when checking `f(...)`:

1. check all arguments to `f` that are neither variables nor function calls (e.g. `if b then x else f(x)`)
2. check all arguments to `f` that are function calls, making a list of any newly borrowed variables from these arguments
3. check all arguments to `f` that are variables, potentially discharging any borrowed variables from step 2

## Function methods

Function methods currently lack some abilities of methods.

### Returning mixtures of shared and linear from function methods

Methods can return mixtures of linear and shared results:

```dafny
method M(...) returns(linear x:X, shared y:Y)
```

Currently, function methods can return a linear result or a shared result, but not both.
To return both, a function method would have to return a tuple with both a linear and a shared field,
and this is not currently allowed:
- a shared tuple cannot contain linear fields, because shared tuples can be duplicated and linear fields cannot be duplicated
- a linear tuple cannot contain shared fields,
because hiding a shared value in a linear tuple could cause the shared value to escape its restricted scope

In principle, it should be possible to have shared fields in linear datatypes,
as long as these are restricted in the same way as shared variables.
Just as a shared value can't escape the scope of a borrowing,
a linear tuple of type `(linear X, shared Y)` would also be disallowed from escaping a borrowing.
However, the type system would have to be careful with polymorphism:
if a type variable `A` could be instantiated with `(linear X, shared Y)`,
then the type system might need special kinds to track which type variables have shared fields,
as in Cogent (see [RelatedWork.md](RelatedWork.md)).
An alternative to kinds would be a `shared linear` annotation,
which would be like `linear` but with the additional restrictions of `shared`:

```dafny
function method F(...): (shared linear pair: (linear X, shared Y))
```

### Function methods with inout

Function methods can perform operations like `SeqUpdate` that semantically appear functional
but are implemented with in-place update.
However, in-place updates like `Replace` and `Swap` (see [Library.md](Library.md))
are currently unavailable to function methods because `inout` arguments
only work for methods, not function methods.
It's not obvious how to combine `inout` with purely functional code in a clean way.

## Linear ghost

`linear ghost` variables could be useful for two reasons:

1. Code can use `linear` to represent separation-logic/alias-type style permissions/capabilities,
such as permission to access an area of memory.
A linear variable representing a permission/capability should be ghost, with no run-time overhead.
2. For code that uses separation-logic style permissions,
linear-logic or separation-logic styles of proof can be used to reason about and rearrange permissions.

`linear ghost` variables should be assignable to `ghost` variables, but not vice-versa.
It's not clear whether `linear` variables should be assignable to `linear ghost` variables;
it would seem strange for a physical object in a `linear` variable to simply disappear into the ghost world
as part of an assignment to `linear ghost`.

For supporting 1., it's not necessary for ghost code to manipulate `linear ghost` variables at all.
For supporting 2., linear Dafny would have to track linearity in ghost code, which it currently does not do.

## Linearity polymorphism

Languages like Linear Haskell emphasize code reuse between nonlinear and linear code
(see [RelatedWork.md](RelatedWork.md)).
Part of this is based on multiplicity variables that provide polymorphism over linearity.
Such a feature in linear Dafny might look like:

```dafny
'L datatype XList<A, 'L> = Nil | Cons(hd: A, 'L tl: LList<A>)
type List<A> = XList<A, ordinary>
type LList<A> = XList<A, linear>

// Length works for 'L = shared or 'L = ordinary
function method Length<A, 'L in shared, ordinary>('L s: XList<A, 'L>): nat {
    shared match s {
        case Nil => 0
        case Cons(_, tl) => 1 + Length(tl)
    }
}
```

The compiler would need to deal with multiplicity polymorphism.
For example, the compiler could require that linear and ordinary values be compiled the same way.
(This is currently not required -- for example, the compiler can currently arrange for ordinary values to be reference counted,
but for linear values to be explicitly freed.)

## Destructors

"Affine" type systems allow discarding but not duplicating values.
Rust, for example, allows a variable to simply go out of scope without being consumed,
and the Rust compiler automatically inserts a call to the variable's destructor.

Linear Dafny does not have destructors and it does not allow linear variables to be discarded.
There are tradeoffs with this design.
On the positive side, linear Dafny can track availability of array elements precisely with no run-time overhead.
Linear Dafny programs can `Take` values from an array, leaving the array element unavailable.
Freeing the array requires that all elements are unavailable,
so there's no need for the array deallocation (`SeqFree`) to try to figure out at run-time which elements are available and call their destructors.
On the negative side, explicitly deallocating all linear values requires extra work from programmers.
Furthermore, methods that are generic over type `A` can't easily deallocate values of type `A`
(for example, see `SwapLinear` in [Library.md](Library.md)).

## Linear in lambdas

Linear Dafny lambdas (`x => expression`) do not yet support linearity:
the parameter `x` cannot be linear or shared, and no linear variables or shared variables can
be captured by the lambda.
Allowing `x` to be linear or shared should be straightforward and would be useful.
Allowing linear/shared variable capture requires some care to make sure linear variables aren't duplicated
and shared variables don't escape.
For example, linear variable capture could be allowed as long as the lambda itself is linear
(as is common in linear lambda calculi).

