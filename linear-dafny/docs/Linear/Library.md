# Library for linear types

This document presents a small library of types for linear sequences and for boxing linear values
inside ordinary values.
In the future, some of these features could be integrated directly into the linear Dafny language
rather than being in an external library.

## Language features supporting libraries

Linear Dafny includes several language features to support user-defined libraries.

### Operator overloading and inline attribute

Linear Dafny allows user programs to overload the "`| |`", "`[]`", and "`in`" operators
by declaring functions named `operator(| |)`, `operator([])`, and `operator(in)`:

```dafny
function{:inline true} operator([])<A>(s: lseq<A>, i: nat): A
    requires i < |s|
{
    LSeqs(s)[i]
}
```

If the type checker detects that expression `e` in `|e|` or `e[...]` or `... in e`
is a user-defined type rather than a built-in type,
it looks for an `operator(...)` function for `e`'s type and replaces
the `|e|` or `e[...]` or `... in e` with a call to the operator function.

The `{:inline true}` attribute on a function `F` indicates that uses of `F`
are inlined in SMT queries.  This can help avoid issues with Dafny or Z3 choosing bad triggers.
(Caveat: the current implementation of this attribute is limited,
supporting only simple function bodies made of function calls and operators,
not arbitrary boolean expressions or arithmetic,
but this could be fixed with more implementation work.)

### rank_is_less_than

Dafny `decreases` work for sequences and inductive datatypes as well as integers.
Linear Dafny also allows user-declared abstract types to appear in decreases clause
via a predicate `rank_is_less_than`:

```dafny
predicate rank_is_less_than<A, B>(a: A, b: B)
```

If `rank_is_less_than(a, b)` is true, then `a` is strictly smaller than `b`,
which can be exploited by `decreases` clauses.
User-declared abstract types can provide axioms about `rank_is_less_than`:

```dafny
type{:extern ...} lseq<A> // externally provided abstract type
function{:axiom} LSeqs<A>(l: lseq<A>): (s: seq<A>)
    ensures rank_is_less_than(s, l) // the sequence s is smaller in rank than the lseq containing it
```

The Boogie prelude file `DafnyPrelude.bpl` takes `rank_is_less_than` into account
when ranking sequences and boxed data values.

### caller_must_be_pure

```dafny
function method{:caller_must_be_pure} F(...): (shared a: A)
```

The attribute `{:caller_must_be_pure}` on a function method `F` indicates that
the function method can only be called in limited situations:

- `F` can be called from ghost code
- `F` can be called from a function method `G` that does not return a `shared` result
- `F` can be called from a function method `G` that is also marked `{:caller_must_be_pure}`
(even if `G` returns a `shared` result)
- `F` can be called from an argument to a call to a method `M` that has no modifies clause and no shared return values

The result of these restrictions is that `F`'s shared return value cannot escape
into any code that performs heap modifications.
This feature is used to allow borrowing from boxed linear values (see below),
which is only safe if the heap-allocated box isn't modified during the borrowing.

The design of this feature depends closely on the semantics of standard Dafny's modifies clauses.
In particular, it exploits the fact that a method with no modifies cannot perform any
heap modifications
(even if the method reverts all of its modifications to leave the heap in its original state).
If methods without modifies clauses could modify the heap,
`caller_must_be_pure` would have to be changed to disallow calls to methods.

## Swapping and assignment via inout

The following methods are convenient for updating linear fields of datatypes:

```dafny
method Replace<V>(linear inout v: V, linear newV: V) returns (linear replaced: V)
    ensures replaced == old_v
    ensures v == newV
{
    replaced := v;
    v := newV;
}

method Swap<V>(linear inout a: V, linear inout b: V)
    ensures b == old_a
    ensures a == old_b
{
    b := Replace(inout a, b);
}
```

For example:

```
linear datatype LList<A> = LNil | LCons(hd: A, linear tl: LList<A>)

method M(linear inout l: LList<int>) {
    if (l.LCons?) {
        inout l.hd := 10;
        inout l.hd := l.hd + 20;

        linear var tmp := Replace(inout l.tl, LNil);
        Swap(inout l.tl, inout tmp);
        linear var LNil() := tmp;

        assert l == old_l.(hd := 30);
    }
}
```

## The seq type

Linear Dafny uses standard Dafny's `seq` type for both ordinary operations
(as in standard Dafny) and linear/shared operations.
The read-only operations `SeqLength` and `SeqGet`
use shared `seq` while read-write operations use linear `seq`.
`SeqUnleash` converts a linear `seq` into an ordinary `seq`,
but otherwise linear/shared `seq` values do not interact with ordinary `seq` values:

```dafny
function method SeqLength<A>(shared s: seq<A>): (n: nat)
    ensures n == |s|

function method SeqGet<A>(shared s: seq<A>, i: nat): (a: A)
    requires i < |s|
    ensures a == s[i]

function method SeqUpdate<A>(linear s: seq<A>, i: nat, a: A): (linear s': seq<A>)
    requires i < |s|
    ensures s' == s[i := a]

method SeqSet<A>(linear inout s: seq<A>, i: nat, a: A)
    requires i < |old_s|
    ensures s == old_s[i := a]
{
    s := SeqUpdate(s, i, a);
}

function method SeqAlloc<A>(length: nat, a: A): (linear s: seq<A>)
    ensures |s| == length
    ensures forall i :: 0 <= i < |s| ==> s[i] == a

function method SeqFree<A>(linear s: seq<A>): ()

function method SeqUnleash<A>(linear s1: seq<A>): (s2: seq<A>)
    ensures s1 == s2
```

Note that linear `seq` values contain ordinary elements, not linear elements,
which allows `SeqUpdate` and `SeqGet` to safely copy elements in and out of the sequence
(see `lseq` below for sequences of linear elements).

The following example uses immutable borrowing in `i < SeqLength(s)`
mutable borrowing in `SeqSet(inout s, i, i)`,
and ghost code (e.g. `s[j] == j`):

```dafny
method Example() returns(x: seq<int>)
    ensures forall i :: 0 <= i < |x| ==> x[i] == i
{
    linear var s := SeqAlloc(10, 0);
    var i := 0;
    while i < SeqLength(s)
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> s[j] == j
    {
        SeqSet(inout s, i, i);
        i := i + 1;
    }
    x := SeqUnleash(s);
}
```

## The lseq type

Elements of linear/shared `seq` are ordinary values, not linear values,
so that `seq` can support copying of values into and out of the sequence elements.
Sequences with linear elements do not allow such copying,
but instead use different operations, such as swap, that are safe for linear values.

The type `lseq` describes sequences of linear elements.
While all elements of a `seq` are available for reading,
`lseq` elements may be present or absent.
The ghost operation `LSeqHas` reports which elements are present,
and `LSeqs` returns the present elements (or arbitrary values for absent elements).
An axiom `LSeqsExtensional` says that `lseq`s with identical elements
are identical.

```dafny
type lseq<A>

function LSeqs<A(00)>(l: lseq<A>): (s: seq<A>) // contents of an lseq, as ghost seq
    ensures rank_is_less_than(s, l)

function LSeqHas<A(00)>(l: lseq<A>): (s: seq<bool>)
    ensures |s| == |LSeqs(l)|

lemma LSeqsExtensional<A(00)>(l1: lseq<A>, l2: lseq<A>)
    requires LSeqs(l1) == LSeqs(l2)
    requires LSeqHas(l1) == LSeqHas(l2)
    ensures l1 == l2
```

For convenience, the following function declarations overload
the `| |` operator, the `[]` operator, and the `in` operator for `lseq`
(all are defined with `inline true` to make sure that their usage doesn't
interfere with Dafny's trigger selection for quantifiers):

```dafny
function{:inline true} operator(| |)<A(00)>(s: lseq<A>): nat
{
    |LSeqs(s)|
}

function{:inline true} operator([])<A(00)>(s: lseq<A>, i: nat): A
    requires i < |s|
{
    LSeqs(s)[i]
}

// Note: it might make more sense to define this as i < |s| && LSeqHas(s)[i],
// but {:inline true} can't yet handle this.
function{:inline true} operator(in)<A(00)>(s: lseq<A>, i: nat): bool
    requires i < |s|
{
    LSeqHas(s)[i]
}
```

All elements of newly allocated `lseq` values are absent.
To free an `lseq`, all elements must be absent so that no linear element values are discarded:

```dafny
method LSeqAlloc<A(00)>(length: nat) returns(linear s: lseq<A>)
    ensures |s| == length
    ensures forall i: nat | i < length :: i !in s

method LSeqFree<A(00)>(linear s: lseq<A>)
    requires forall i: nat | i < |LSeqs(s)| :: i !in s
```

The following readonly functions can get the length, as an ordinary integer,
or borrow an element, as a shared value:

```dafny
function method LSeqLength<(00)A>(shared s: lseq<A>): (n: nat)
    ensures n == |s|

function method LSeqGet<A(00)>(shared s: lseq<A>, i: nat): (shared a: A)
    requires i < |s| && i in s
    ensures a == s[i]
```

Mutations on `lseq` elements are either take, give, or swap operations.
Giving an element to the `lseq` sets the corresponding `LSeqHas` to true,
making the element present, while taking sets it to `false`, making the element absent:

```dafny
method LSeqGive<A(00)>(inout linear s: lseq<A>, i: nat, linear a: A)
    requires i < |old_s| && i !in old_s
    ensures LSeqHas(s) == LSeqHas(old_s)[i := true]
    ensures LSeqs(s) == LSeqs(old_s)[i := a]

method LSeqTake<A(00)>(linear inout s: lseq<A>, i: nat) returns(linear a: A)
    requires i < |old_s| && i in old_s
    ensures LSeqHas(s) == LSeqHas(old_s)[i := false]
    ensures LSeqs(s) == LSeqs(old_s)
    ensures a == old_s[i]

method LSeqSwap<A(00)>(inout linear s: lseq<A>, i: nat, linear a1: A) returns(linear a2: A)
    requires i < |old_s| && i in old_s
    ensures a2 == LSeqs(old_s)[i]
    ensures LSeqs(s) == LSeqs(old_s)[i := a1]
```

The following example shows both mutation and readonly operations on `lseq` values:

```dafny
method LSeqExample<A(00)>(linear inout s: lseq<LList<A>>) returns(linear lens: seq<int>)
    requires forall i: nat | i < |old_s| :: i in old_s
    ensures s == old_s
    ensures |lens| == |s|
    ensures forall i: nat | i < |lens| :: lens[i] == Length(s[i])
{
    // Compute length of every list in s
    var len := LSeqLength(s);
    lens := SeqAlloc(len, 0);
    var i: nat := 0;
    while (i < len)
        invariant i <= len
        invariant s == old_s
        invariant |lens| == len
        invariant forall j: nat | j < i :: lens[j] == Length(s[j])
    {
        if (*)
        {
            // The hard way to do it:
            linear var l: LList<A>;
            l := LSeqTake(inout s, i);
            SeqSet(inout lens, i, Length(l));
            LSeqGive(inout s, i, l);
            LSeqsExtensional(old_s, s);
        }
        else
        {
            // The easy way to do it:
            SeqSet(inout lens, i, Length(LSeqGet(s, i)));
        }
        i := i + 1;
    }
}
```

## Boxed linear values

Linear datatypes can contain ordinary fields.
The opposite is not allowed: you can't put a linear field in an ordinary datatype,
because ordinary datatypes can be duplicated and discarded,
which duplicates and discards the datatype's fields.
However, we can define a special linear-to-ordinary adapter object that holds linear data.
The adapter object lives in the heap.
Since the heap can't be duplicated, the object can't be duplicated and its linear data can't be duplicated.
The linear data in the object is only usable via a Swap method that swaps
one linear value for another:

```dafny
class SwapLinear<A(00)>
{
    function Read(): A
        reads this

    constructor(linear a: A)
        ensures Read() == a

    method Swap(linear a1: A) returns(linear a2: A)
        modifies this
        ensures a2 == old(Read())
        ensures Read() == a1
}
```

However, this simply definition of `SwapLinear` has two deficiencies.
First, it can leak linear values.
If a program creates a `SwapLinear` object `x` to hold a linear value `a`,
then `x` can simply be discarded, since it is an ordinary heap object.
Discarding `x`, unfortunately, also discards `a`.
To prevent this, it's a good idea to extend `SwapLinear`
to call a destructor that deallocates the `a` value.
There are various ways to arrange this,
but the simplest is to pass a destructor function method of type `(linear A) --> ()`
to the `SwapLinear` constructor:

```dafny
    constructor(linear a: A, destructor: (linear A) --> ())
```

The second deficiency is that accessing the `A` value inside
the `SwapLinear` requires a call to `Swap`,
which always modifies the `SwapLinear` object.
This is inconvenient for methods or function methods that use the `A` value read-only:

```dafny
linear datatype LOption<A> = LNone | LSome(linear a: A)

method BorrowInt(shared s: int)

method ReadInt(swap: SwapLinear<LOption<int>>)
    requires swap.Read().LSome?
    modifies swap; // annoying, since we're only reading from "swap"
    ensures swap.Read() == old(swap.Read())
{
    linear var x := swap.Swap(LNone);
    BorrowInt(x.a);
    linear var empty := swap.Swap(x);
    linear var LNone() := empty;
}
```

The following definition adds a `Borrow` function method
that returns a shared `A`:

```dafny
class SwapLinear<A(00)>
{
    function Inv(): (A) -> bool
        reads this

    function Read(): (a: A)
        reads this
        ensures Inv()(a)

    constructor(linear a: A, destructor: (linear A) --> ())
        requires destructor.requires(a)
        ensures Inv() == destructor.requires
        ensures Read() == a

    method Swap(linear a1: A) returns(linear a2: A)
        requires Inv()(a1)
        modifies this
        ensures Inv() == old(Inv())
        ensures a2 == old(Read())
        ensures Read() == a1

    function method{:caller_must_be_pure} Borrow(): (shared a: A)
        reads this
        ensures a == Read()
}

method ReadInt(swap: SwapLinear<LOption<int>>)
    requires swap.Read().LSome?
{
    BorrowInt(swap.Borrow().a);
}
```

`Borrow` relies on the `{:caller_must_be_pure}` attribute (see above)
to prevent the shared `A` from leaking into code that
could modify the `SwapLinear` object,
since such a modification would allow the `shared A` to coexist with a `linear A`,
which would be unsafe:

```dafny
method ReadInt''(swap: SwapLinear<LOption<int>>)
    requires swap.Read().LSome?
    modifies swap
{
    shared var x := swap.Borrow(); // FAILS ("Error: cannot call caller_must_be_pure function method
                                   // from method except as an argument to a method with no modifies
                                   // or shared returns")
    linear var y := swap.Swap(LNone);
    // x would coexist with y here
    ...
}
```

The following example wraps `SwapLinear` in a class `BoxedLinear` that
hides the `Swap` operation in favor of `Take` and `Give` methods:

```dafny
linear datatype LOption<A> = LNone | LSome(linear a: A)

class BoxedLinear<A(00)>
{
    var data: SwapLinear<LOption<A>>;

    function Has(): bool
        reads this, data
    {
        data.Read().LSome?
    }

    function Read(): A
        reads this, data
    {
        var a: A :| true;
        match data.Read() case LNone => a case LSome(a) => a
    }

    constructor (destructor: (linear LOption<A>) --> ())
        requires destructor.requires(LNone)
        ensures !Has()
        ensures fresh(this.data)
        ensures data.Inv() == destructor.requires
    {
        data := new SwapLinear(LNone, destructor);
    }

    method Take() returns(linear a: A)
        modifies this, data
        requires Has()
        requires data.Inv()(LNone)
        ensures !Has()
        ensures a == old(Read())
        ensures data == old(data)
        ensures data.Inv() == old(data.Inv())
        ensures data.Inv()(LSome(a))
    {
        linear var x := data.Swap(LNone);
        linear var LSome(y) := x;
        a := y;
    }

    method Give(linear a: A)
        modifies this, data
        requires !Has()
        requires data.Inv()(LSome(a))
        ensures Has()
        ensures a == Read()
        ensures data == old(data)
        ensures data.Inv() == old(data.Inv())
    {
        linear var x := data.Swap(LSome(a));
        linear var LNone() := x;
    }

    function method{:caller_must_be_pure} Borrow(): (shared a: A)
        reads this, data
        requires Has()
        ensures a == Read()
        ensures data.Inv()(LSome(a))
    {
        data.Borrow().a
    }
}

linear datatype D = D(i: int, j: int)

function method D_Destructor(linear d: LOption<D>): () {
    linear match d case LNone => () case LSome(D(i, j)) => ()
}

method BoxedLinearExample(linear inout d: D)
{
    var box1 := new BoxedLinear(D_Destructor);
    box1.Give(d);
    var box2 := new BoxedLinear(D_Destructor);
    var box3 := box1; // box1 is not linear, so we can duplicate it
    d := box1.Take();

    // This following would fail, because box3 == box1 and we already took the D out of box1:
    // linear var d' := box3.Take();
    // box3.Give(d');
}
```
