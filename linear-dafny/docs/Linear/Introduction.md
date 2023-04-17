# A linear type system for Dafny

This document describes a linear type system that extends Dafny's original type system.

Throughout this document, the term *linear Dafny* refers to the Dafny implementation
with the linear type system, and *standard Dafny* refers to Dafny without the linear type system.

## Why linearity?

Standard Dafny supports both immutable data structures (e.g. `datatype` and `seq`)
and mutable data structures (e.g. `class` and `array`).
Programs with mutable data structures are often more difficult to verify,
because of aliasing and mutation: two variables may refer to the same object,
and therefore a write to one variable may affect reads from another variable:

```dafny
method M(x: array<int>, y: array<int>)
    requires x.Length == y.Length == 10
    requires x[3] == 30
    modifies y
{
    assert x[3] == 30; // ok
    y[3] := 31; // in-place update
    assert x[3] == 30; // FAILS: update to y might have affected x
}
```

Programs based on immutable data structures do not have to worry about aliasing and mutation.
Without mutation, though, programs may have to copy a data structure to update the data structure:

```dafny
method M(x: seq<int>, y: seq<int>) returns(y': seq<int>)
    requires |x| == |y| == 10
    requires x[3] == 30
{
    assert x[3] == 30; // ok
    y' := y[3 := 31]; // copy entire sequence
    assert x[3] == 30; // ok
}
```

Ideally, we'd like to have the best of both worlds:
the efficient in-place mutations of mutable data structures
and the easier verification of immutable data structures.
That is, we'd like the Dafny verifier to treat data structures as immutable
and the Dafny compiler to treat data structures as mutable to perform in-place updates.
In general, this combination would not be sound.
However, there's an important special case:
if the compiler knows that there's only one reference to an object (i.e. no aliases),
it can perform an in-place update without invalidating any assertions made by the verifier.

Linear type systems provide a way to express this "no aliasing" constraint
so that the compiler can safely perform in-place updates.
A variable tagged as `linear` in linear Dafny is guaranteed to hold the only reference to the data:

```dafny
function method SeqUpdate<A>(linear s: seq<A>, i: nat, a: A): (linear s': seq<A>)
    requires i < |s|
    ensures s' == s[i := a]

method M(linear x: seq<int>, linear y: seq<int>) returns(linear x': seq<int>, linear y': seq<int>)
    requires |x| == |y| == 10
    requires x[3] == 30
{
    assert x[3] == 30; // ok
    y' := SeqUpdate(y, 3, 31); // in-place update
    assert x[3] == 30; // ok
    x' := x;
}
```

Since `x` and `y` are linear variables of type `seq<int>`,
each contains a unique, unaliased reference to a sequence of integers.
Therefore, the linear Dafny compiler knows that an update to `y` (namely, `y' := SeqUpdate(y, 3, 31)`)
can be implemented in-place without disturbing `x`.
To the linear Dafny verifier, the update looks like an ordinary standard Dafny copy (`y' := y[3 := 31]`).
In fact, linear Dafny makes no changes to the verification process:
linear Dafny generates the same SMT queries (satisfiability modulo theories queries) as standard Dafny would,
with changes only to type checking and compilation.

The linear Dafny type checker enforces the no-aliasing property on `linear` variables.
To do this, the type checker forbids duplication and discarding of `linear` variables.
For example, it is a type error to try to pass the same linear variable `z` twice in a method call (shown in `N1`),
or to try to copy `z` into two coexisting local variables `x` and `y` (shown in `N2`):

```dafny
method M(linear x: seq<int>, linear y: seq<int>)

method N1(linear z: seq<int>) {
    M(z, z); // FAILS: cannot duplicate linear variable z
}

method N2(linear z: seq<int>) {
    linear var x := z; // ok, consumes z
    linear var y := z; // FAILS: z was already consumed by x, so it is not available for y
    M(x, y);
}
```

Because linear variables are neither duplicated nor discarded,
it's common to pass them as arguments and also return them as return values:

```dafny
method M(linear x: seq<int>, linear y: seq<int>) returns(linear x': seq<int>, linear y': seq<int>)
```

To make this more convenient, linear Dafny supports `inout` parameters:

```dafny
method SeqSet<A>(linear inout s: seq<A>, i: nat, a: A)
    // TODO: currently, one has to write old_s instead of s and old(s), but the goal is to support s and old(s)
    requires i < |s|
    ensures s == old(s)[i := a]
{
    s := SeqUpdate(s, i, a);
}

method M(linear inout x: seq<int>, linear inout y: seq<int>)
    requires |x| == |y| == 10
    requires x[3] == 30
    ensures x == old(x)
    ensures y == old(y)[3 := 31]
{
    assert x[3] == 30; // ok
    SeqSet(inout y, 3, 31); // in-place update
    assert x[3] == 30; // ok
}
```

To the Dafny verifier, `inout` parameters appear as both arguments and return values.
(For efficiency, though, the Dafny compiler treats `inout` parameters as pass-by-reference.)

The no-aliasing property is restrictive.
Sometimes, it's useful to temporarily allow aliases, as long as mutation is disallowed.
Therefore, linear Dafny also supports aliasiable, immutable `shared` variables
that are temporarily *borrowed* from `linear` variables:

```dafny
method M(shared x1: seq<int>, shared x2: seq<int>, linear inout y: seq<int>)
    requires |x1| == |x2| == |y| == 10
    requires x1[3] == 30
{
    assert x1[3] == 30; // ok
    SeqSet(inout y, 3, 31); // in-place update
    assert x1[3] == 30; // ok
}

method N(linear inout x: seq<int>, linear inout y: seq<int>)
    requires |x| == |y| == 10
    requires x[3] == 30
{
    M(x, x, inout y); // borrow from linear x to instantiate shared x1, x2
}
```

Unlike `linear` variables, `shared` variables may be freely duplicated and discarded.
The scope of such `shared` variables is restricted so that they cannot coexist with
the linear variable that they borrow from.
This ensures that at any place in a program, a value can either be held
in a single `linear` variable or multiple `shared` variables, but not both.

## Linear variables and shared variables

Each Dafny variable is one of the following:
  - `ghost`
  - `linear`
  - `shared`
  - ordinary (no annotation)

For example:
```dafny
    ghost var xg: T;
    linear var xl: T;
    shared var xs: T;
    var xo: T;
```

Ghost, linear, shared, and ordinary variables may be assigned to ghost variables:
```dafny
    xg := xg';
    xg := xl';
    xg := xs';
    xg := xo';
```

Linear variables may be assigned to linear variables:
```dafny
    xl := xl';
```

Shared variables may be assigned to shared variables:
```dafny
    xs := xs';
```

Ordinary variables may be assigned to ordinary variables:
```dafny
    xo := xo';
```

Other assignments are disallowed
(except for a special case of "borrowing" linear variables into shared variables, described below).

Linear variables cannot be duplicated.
The following is disallowed because it tries to duplicate xl:
```dafny
  linear var xl := ...;
  linear var xl1 := xl;
  linear var xl2 := xl;
```

Linear variables cannot be discarded.
The following is disallowed because it tries to discard xl at the end of a block:
```dafny
  {
    linear var xl := ...;
    // xl discarded at end of block
  }
```

At any place in a program, a linear variable is either "available" or "unavailable".
When a linear variable is assigned, it becomes available.
When a linear variable is used, it becomes unavailable (it is "consumed" by the use).
It is illegal to use an unavailable variable, except in ghost code; this prevents duplication.
It is illegal to let an available variable go out of scope; this prevents discarding.
For example:
```dafny
  linear var xl := ...;
  // xl is available
  linear var xl1 := xl; // ok, because xl is available here
  // xl is unavailable, xl1 is available
  linear var xl2 := xl; // illegal: tries to use xl, which is unavailable here
  ghost var xg := xl; // ok: ghost code can use unavailable variables
```

All linear input parameters are assumed to be available at method entry.
All linear return values must be available at method exit:

```dafny
method M(linear x: seq<int>) returns(linear x': seq<int>) {
    // x is available
    x' := x;
    // x consumed, x' now available
}
```

## Tuples and datatypes

Standard Dafny has tuple types `(t1, ..., tn)`, for types `t1` ... `tn`,
with tuple constructors `(e1, ..., en)`, for expressions `e1` ... `en`,
and pattern matching to deconstruct tuples.
Linear Dafny extends these tuples to allow `linear` and `ghost` fields,
using `linear t` or `ghost t` in the field types and `linear e` or `ghost e` in the constructor fields:

```dafny
method M(linear inout x: seq<int>, y: int, ghost g: int) {
    linear var z: (linear seq<int>, int, ghost int);
    z := (linear x, y, ghost g);
    linear var (x', y', g') := z;
    x := x';
}
```

A tuple with one or more linear fields is itself linear: it can be stored in a linear variable,
like `z` in the code above, but not in an ordinary variable.

In addition to `linear` tuples, user-defined datatypes may be declared `linear`,
and `linear` datatypes may contain `linear` fields.
An constructor for a `linear` datatype produces a `linear` value,
and a `linear match` deconstructs a linear datatype value:

```dafny
linear datatype LOption<A> = LNone | LSome(linear a: A)
linear datatype LList<A> = LNil | LCons(hd: A, linear tl: LList<A>)

function method IncrAll(linear l: LList<int>): linear LList<int> {
    linear match l {
        case LNil => LNil
        case LCons(hd, tl) => LCons(hd + 1, IncrAll(tl))
    }
}

method IncrAllHere(inout linear l: LList<int>) {
    if l.LCons? {
        inout l.hd := l.hd + 1;
        IncrAllHere(inout l.tl);
    }
}
```

A `linear match` consumes and deallocates the linear value that it deconstructs,
so that the `IncrAll` method shown above recursively deallocates an entire linear list
and generates a new linear list.

It's also possible to update linear datatypes in place.
An `inout x.f := ...` statement performs an in-place update of an ordinary field `f` of a linear datatype x,
as shown above in the `IncrAllHere` method,
which recursively updates an entire linear list without deallocating it or allocating a new list.

Tuple and datatype fields cannot be declared `shared`.
(This prevents `shared` variables from escaping their original scope.)
However, a program can borrow from a `linear` reference to a linear datatype,
resulting in a `shared` reference to the linear datatype.
Any `linear` fields in such a `shared` reference act like `shared` fields,
producing a `shared` result.
For example, the linear `tl` field appears as `shared` in the `shared` pattern match in
`Length` and the field access `s.tl` in `Length'`:

```dafny
linear datatype LOption<A> = LNone | LSome(linear a: A)
linear datatype LList<A> = LNil | LCons(hd: A, linear tl: LList<A>)

function method Length<A>(shared s: LList<A>): nat {
    shared match s {
        case LNil => 0
        case LCons(_, tl) => 1 + Length(tl) // tl is a shared LList<A>, not a linear LList<A>
    }
}

// Alternate implementation:
function method Length'<A>(shared s: LList<A>): nat {
    if s.LNil? then 0
    else 1 + Length'(s.tl) // s.tl is a shared LList<A>, not a linear LList<A>
}
```

## Shared variables and borrowing

An expression or method call may *borrow* a linear variable `x`
so that `x` appears as `shared` (immutable borrowing) or `inout` (mutable borrowing) within the expression or method call.
After the expression or method call, `x` becomes `linear` again.
The `MakeEven` and `CallCompute` demonstrate borrowing in an expression and in a method call:

```dafny
linear datatype LOption<A> = LNone | LSome(linear a: A)
linear datatype LList<A> = LNil | LCons(hd: A, linear tl: LList<A>)

function method Length<A>(shared s: LList<A>): nat {
    shared match s {
        case LNil => 0
        case LCons(_, tl) => 1 + Length(tl)
    }
}

function method MakeEven(linear l: LList<int>): linear LList<int> {
    var len: int := Length(l); // borrow linear l as shared inside expression Length(l)
    if len % 2 == 0 then l else LCons(0, l)
}

method ComputeLength<A>(shared s: LList<A>) returns(n: nat)
    ensures n == Length(s)
{
    n := 0;
    shared var iter := s;
    while iter.LCons?
        invariant n + Length(iter) == Length(s)
        decreases Length(iter)
    {
        n := n + 1;
        iter := iter.tl;
    }
}

method CallCompute(linear inout l: LList<int>) {
    var n := ComputeLength(l); // borrow linear argument l as shared inside method call ComputeLength(l)
}
```

When checking an expression or method call, linear Dafny tracks the state of each linear variable,
where the state is either available, borrowed, or consumed:

- Using an available variable as an argument to a `linear` function/method parameter makes the variable consumed.
A consumed variable cannot be borrowed or used linearly.  It can, however, be used as a ghost value.
- Using an available variable as an argument to a `linear inout` method parameter makes the variable borrowed mutably.
An mutably borrowed variable cannot be duplicated and cannot be used linearly.  It can, however, be used as a ghost value.
- Using an available variable as an argument to a `shared` function/method parameter makes the variable borrowed immutably.
An immutably borrowed variable can be duplicated, but it cannot be used linearly.  It can also be used as a ghost value.

For example, the following method call `M(x, x, 10)` is ok, because `x` can be borrowed more than once,
but the subsequent method call `M(x, x, F(x))` has a type error, because `x` cannot be both borrowed and consumed:

```dafny
function method F(linear x: int): int
method M(shared x: int, shared y: int, i: int)

method N(linear inout x: int) {
    M(x, x, 10); // ok
    M(x, x, F(x)); // FAILS: x cannot be used linearly in F(x) after being borrowed by first two arguments
}
```

If an expression or method call produces a `shared` result, the expression or call is not allowed to borrow any `linear` variables as `shared`.
This ensures that the borrowed value stays confined in the expression or call, and doesn't escape outside
where it could coexist unsafely with the original `linear` variable.
Note that if an expression or call does not borrow any arguments, it may produce `shared` results:

```dafny
method M1(shared s: int) returns(shared s': int)
method M2(shared s: int) returns(s': int)

method N(linear inout x: int, shared y: int) {
    shared var y1 := M1(y); // ok: no borrowing
    var y2 := M2(x); // ok: no shared return value
    shared var y3 := M1(x); // FAILS: can't borrow and return shared result
}
```

Future versions of linear Dafny could allow borrowing in more places.
Allowing a statement to borrow from a linear variable would be particularly useful:

```dafny
method M(linear l: LList<int>) {
    {
        shared var s := l; // would be useful, but is not yet supported
        ...use s...
    }
    ...use l...
}
```

To work around the lack of statement-level borrowing, a program can use a method call:

```dafny
method M'(shared s: LList<int>) {
    ...use s...
}

method M(linear l: LList<int>)
{
    M'(l);
    ...use l...
}
```

