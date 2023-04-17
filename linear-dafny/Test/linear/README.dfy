// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
This file describes an experimental "linearity" extension to Dafny.
With this extension, Dafny programs can declare "linear variables",
which cannot be duplicated and cannot be discarded.
This allows programs to express in-place updates of functional data structures.
It also allows manual memory management of functional data structures.

Each Dafny variable is one of the following:
  - "ghost"
  - "linear"
  - "shared"
  - ordinary (no annotation)
For example:
    ghost var xg:T;
    linear var xl:T;
    shared var xs:T;
    var xo:T;

Ghost, linear, shared, and ordinary variables may be assigned to ghost variables:
    xg := xg';
    xg := xl';
    xg := xs';
    xg := xo';
Linear variables may be assigned to linear variables:
    xl := xl';
Shared variables may be assigned to shared variables:
    xs := xs';
Ordinary variables may be assigned to ordinary variables:
    xo := xo';
Other assignments are disallowed
(except for a special case of "borrowing" linear variables into shared variables, described below).
*/

method Vars<T>(ghost xg_in:T, linear xl_in:T, shared xs_in:T, xo_in:T) returns(linear xl_out:T)
{
    ghost var xg:T;
    linear var xl:T;
    shared var xs:T;
    var xo:T;

    xg := xg_in;
    xg := xl_in;
    xg := xs_in;
    xg := xo_in;
    xl := xl_in;
    xs := xs_in;
    xo := xo_in;

    xl_out := xl;
}

/*
Linear variables cannot be duplicated.
The following is disallowed because it tries to duplicate xl:
  linear var xl := ...;
  linear var xl1 := xl;
  linear var xl2 := xl;
Linear variables cannot be discarded.
The following is disallowed because it tries to discard xl at the end of a block:
  {
    linear var xl := ...;
    // xl discarded at end of block
  }
At any place in a program, a linear variable is either "available" or "unavailable".
When a linear variable is assigned, it becomes available.
When a linear variable is used, it becomes unavailable (it is "consumed" by the use).
It is illegal to use an unavailable variable; this prevents duplication.
It is illegal to let an available variable go out of scope; this prevents discarding.
For example:
  linear var xl := ...;
  // xl is available
  linear var xl1 := xl; // ok, because xl is available here
  // xl is unavailable, xl1 is available
  linear var xl2 := xl; // illegal: tries to use xl, which is unavailable here 
Notice that the "Vars" method shown above returns a linear result "xl_out".
This is because it can't simply let xl go out of scope while it is still available;
it must assign xl to some other variable, like xl_out.
Furthermore, any linear return values like xl_out must be available at method exit.
Any linear input parameters like xl_in are assumed to be available at method entry.
*/

/*
Datatypes may be declared linear:
*/
linear datatype ld = LD(i:int)

/*
A constructor of a linear datatype produces a linear value that can be stored in a linear variable:
*/
method Test_ld_1() returns(linear x:ld)
{
    x := LD(10);
}

/*
Linear datatypes are deconstructed with linear pattern matching
(or with shared pattern matching, described later):
*/
method Test_ld_2(b:bool, linear x:ld)
{
    if (b)
    {
        linear match x {case LD(i) => print i + i;}
    }
    else
    {
        // Alternate syntax for linear match when there's only one case:
        linear var LD(i) := x;
        print i + i;
    }
}

/*
Linear datatypes may contain linear fields, which store linear values:
*/
linear datatype lOption<A> = LNone | LSome(linear a:A)
linear datatype nlPair<A, B> = NlPair(a:A, linear b:B)
linear datatype llPair<A, B> = LlPair(linear a:A, linear b:B)
linear datatype nlList<A> = NlNil | NlCons(hd:A, linear tl:nlList<A>)

function method IncrAll(linear l:nlList<int>):linear nlList<int>
{
    linear match l
    {
        case NlNil => NlNil
        case NlCons(hd, tl) => NlCons(hd + 1, IncrAll(tl))
    }
}

/*
It is often convenient to temporarily duplicate a linear variable when reading it.
This is supported by "shared" variables, which may temporarily "borrow" a linear variable
for read-only operations.
For example, the Length function below reads a linear list to compute its length.
*/

function method Length<A>(shared s:nlList<A>):int
{
    shared match s
    {
        case NlNil => 0
        case NlCons(_, tl) => 1 + Length(tl)
    }
}

function method MakeEven(linear l:nlList<int>):linear nlList<int>
{
    var len:int := Length(l); // borrow linear l into shared s when calling Length
    if len % 2 == 0 then l else NlCons(0, l)
}

/*
A variable binding expression like "var x := e1; e2" may freely borrow a linear variable l inside e1
as long as it eventually consumes l in e2.
Note that borrowing must strictly precede consumption;
it would be illegal, for example, for "var x := e1; e2" to consume l in e1
and then try to borrow it in e2.
It would also be illegal to consume l and borrow l side by side,
since expression evaluation order is underspecified:
  f(Length(l), IncrAll(l)) // not allowed -- IncrAll could deallocate l before Length reads it, depending on the compiler
To work around this limitation, simply use a temporary variable:
  var len := Length(l);
  f(len, IncrAll(l)) // ok

Here are some additional examples of sharing:
*/

function method Share2(linear l:nlList<int>):linear nlList<int>
{
    var w:int := Length(l) + Length(l);
    var x:int := if l.NlNil? then 0 else l.hd + l.hd;
    var y:int := (
        shared var s := l;
        shared var s1 := s;
        shared var s2 := s;
        Length(s1) + Length(s2)
    );
    var z:int := (
        shared match l
        {
            case NlNil => 0
            case NlCons(sa, sb) => sa + Length(sb)
        }
    );
    NlCons(w + x + y + z, l)
}
/*
There's an important restriction on borrowing in "var x := e1; e2":
a linear variable l may be shared within e1 (and then consumed in e2),
but if e1 borrows any linear variables, x cannot be a shared variable,
so that e1 cannot pass any shared values through x into e2.
For example, "shared var x := l; f(Length(x), IncrAll(l))" is illegal.
This prevents a shared l and a consumed l from living side by side inside e2.
The Share2 method above contains "var y:int := e1; e2",
where e1 = "(shared var s := l; ...)".
This demonstrates that sharing is allowed within e1,
where e1's local variables like s, s1, and s2 are shared,
but y cannot be marked "shared".

Finally, fields of datatypes may be marked linear or ghost, but not shared.
*/

/*
Unfortunately, it is not yet possible for statements to
directly borrow a linear variable into a shared variable:
  method M(linear l:nlList<int>)
  {
      {
          shared var s := l; // would be useful, but is not yet supported
          ...use s...
      }
      ...use l...
  }

Instead, a method can indirectly borrow by calling another method,
as in the example below.
(Important restriction: if a method call borrows a linear argument into
a shared parameter, the method is not allowed to return a shared result.
This prevents the method from trying to return the original linear value
back to the caller as a (duplicated) shared value.)
*/

method Inner<A>(shared s_in:nlList<A>) returns(len:int)
    ensures len == Length(s_in)
{
    shared var s := s_in;
    len := 0;
    while (s.NlCons?)
        invariant Length(s) + len == Length(s_in)
        decreases s
    {
        len := len + 1;
        s := s.tl;
    }
}

method Outer(linear l_in:nlList<int>) returns(linear l:nlList<int>)
{
    l := l_in;
    var len := Inner(l); // ok: borrow l by calling Inner
    var doubleLen := Length(l) + Length(l); // ok: borrow l inside expression
    assert doubleLen == len * 2;
}

/*
In-place updates to sequences are a useful application of linearity.
We can define linear operations on seq<A>, which contains ordinary values,
and on lseq<A>, which contains linear values.

Notice that seq supports get and set, while lseq only supports swap.
This is because get and set duplicate and discard, which is not allowed on linear values,
whereas swap simply exchanges one linear value for another, which is allowed.

To help with swapping, the maybe<A> type optionally holds an A value,
depending on whether the ghost property has(m) is true or false.
Get and set operations for lseq swap a maybe<A> value with has(m) == true for
a maybe<A> value with has(m) == false.
*/

function method seq_get<A>(shared s:seq<A>, i:nat):(a:A)
    requires i < |s|
    ensures a == s[i]
function method seq_set<A>(linear s1:seq<A>, i:nat, a:A):(linear s2:seq<A>) // can be implemented as in-place update
    requires i < |s1|
    ensures s2 == s1[i := a]
function method seq_length<A>(shared s:seq<A>):(n:nat)
    ensures n == |s|

method seq_alloc<A>(length:nat, a:A) returns(linear s:seq<A>)
    ensures |s| == length
    ensures forall i :: 0 <= i < |s| ==> s[i] == a

method seq_free<A>(linear s:seq<A>)

type maybe<A>
predicate has<A>(m:maybe<A>)
function read<A(00)>(m:maybe<A>):A
function method peek<A(00)>(shared m:maybe<A>):(shared a:A)
    requires has(m)
    ensures a == read(m)
function method take<A(00)>(linear m:maybe<A>):(linear a:A)
    requires has(m)
    ensures a == read(m)
function method give<A(00)>(linear a:A):(linear m:maybe<A>)
    ensures has(m)
    ensures read(m) == a
    ensures forall x:maybe<A> {:trigger give(read(x))} | has(x) && a == read(x) :: m == x
function method empty<A>():(linear m:maybe<A>)
    ensures !has(m)
function method discard<A>(linear m:maybe<A>):()
    requires !has(m)

type lseq<A>
function lseqs<A>(l:lseq<A>):(s:seq<maybe<A>>) // contents of an lseq, as ghost seq
    ensures rank_is_less_than(s, l)
function method lseq_length<A>(shared s:lseq<A>):(n:nat)
    ensures n == |lseqs(s)|

method lseq_alloc<A>(length:nat) returns(linear s:lseq<A>)
    ensures |lseqs(s)| == length
    ensures forall i:nat | i < length :: !has(lseqs(s)[i])

method lseq_free<A>(linear s:lseq<A>)
    requires forall i:nat | i < |lseqs(s)| :: !has(lseqs(s)[i])

// can be implemented as in-place swap
method lseq_swap<A>(linear s1:lseq<A>, i:nat, linear a1:maybe<A>) returns(linear s2:lseq<A>, linear a2:maybe<A>)
    requires i < |lseqs(s1)|
    ensures a2 == lseqs(s1)[i]
    ensures lseqs(s2) == lseqs(s1)[i := a1]

function method lseq_share<A>(shared s:lseq<A>, i:nat):(shared a:maybe<A>)
    requires i < |lseqs(s)|
    ensures a == lseqs(s)[i]

function{:inline true} operator(| |)<A>(s:lseq<A>):nat
{
    |lseqs(s)|
}

function{:inline true} operator([])<A(00)>(s:lseq<A>, i:nat):A
    requires i < |s|
{
    read(lseqs(s)[i])
}

function{:inline true} operator(in)<A>(s:lseq<A>, i:nat):bool
    requires i < |s|
{
    has(lseqs(s)[i])
}

function method lseq_peek<A(00)>(shared s:lseq<A>, i:nat):(shared a:A)
    requires i < |s|
    requires i in s
    ensures a == s[i]
{
    peek(lseq_share(s, i))
}

method lseq_take<A(00)>(linear s1:lseq<A>, i:nat) returns(linear s2:lseq<A>, linear a:A)
    requires i < |s1|
    requires i in s1
    ensures a == s1[i]
    ensures lseqs(s2) == lseqs(s1)[i := empty()]
{
    linear var x1:maybe<A> := empty();
    linear var x2:maybe<A>;
    s2, x2 := lseq_swap(s1, i, x1);
    a := take(x2);
}

method lseq_give<A(00)>(linear s1:lseq<A>, i:nat, linear a:A) returns(linear s2:lseq<A>)
    requires i < |s1|
    requires i !in s1
    ensures lseqs(s2) == lseqs(s1)[i := give(a)]
{
    linear var x1:maybe<A> := give(a);
    linear var x2:maybe<A>;
    s2, x2 := lseq_swap(s1, i, x1);
    var _ := discard(x2);
}

method SeqExample<A>(linear s_in:lseq<nlList<A>>) returns(linear s:lseq<nlList<A>>, linear lens:seq<int>)
    requires forall i:nat | i < |s_in| :: i in s_in
    ensures lseqs(s) == lseqs(s_in)
    ensures |lens| == |s|
    ensures forall i:nat | i < |lens| :: lens[i] == Length(s[i])
{
    // Compute length of every list in s_in
    s := s_in;
    var len := lseq_length(s);
    lens := seq_alloc(len, 0);
    var i:nat := 0;
    while (i < len)
        invariant i <= len
        invariant lseqs(s) == lseqs(s_in)
        invariant |lens| == len
        invariant forall j:nat | j < i :: lens[j] == Length(s[j])
    {
        if (*)
        {
            // The hard way to do it:
            linear var l:nlList<A>;
            s, l := lseq_take(s, i);
            lens := seq_set(lens, i, Length(l));
            s := lseq_give(s, i, l);
        }
        else
        {
            // The easy way to do it:
            lens := seq_set(lens, i, Length(lseq_peek(s, i)));
        }
        i := i + 1;
    }
}

/*
Linear datatypes can contain ordinary fields.
The opposite is not allowed: you can't put a linear field in an ordinary datatype,
because ordinary datatypes can be duplicated and discarded,
which duplicates and discards the datatype's fields.
However, we can define a special ordinary adapter object that holds linear data.
The adapter object lives in the heap.
Since the heap can't be duplicated, the object can't be duplicated and its linear data can't be duplicated.
The linear data in the object is only usable via a Swap method that swaps
one linear value for another:
*/
class BoxedLinear<A>
{
    function Read():A
        reads this
    constructor(linear a:A)
        ensures Read() == a
    method Swap(linear a1:A) returns(linear a2:A)
        modifies this
        ensures a2 == old(Read())
        ensures Read() == a1
    function method{:caller_must_be_pure} Borrow():(shared a:A)
        reads this
        ensures a == Read()
}
/*
Note, however, that this adapter doesn't stop an object from being silently discarded
during garbage collection, so it's possible to leak linear data using this adapter.
Also note that Borrow() has a special attribute, caller_must_be_pure, which
requires callers to be functions or function methods (not methods)
and disallows callers from returning shared values (unless the caller is also caller_must_be_pure).
In addition, expressions in arguments to method calls may also call Borrow as long as
the called method has no modifies clause and no shared return values.
These restrictions ensure that Swap cannot be called while using the shared value returned from Borrow.
*/
class MaybeLinear<A(00)>
{
    var box:BoxedLinear<maybe<A>>;
    function Has():bool
        reads this, box
    {
        has(box.Read())
    }
    function Read():A
        reads this, box
    {
        read(box.Read())
    }
    constructor Empty()
        ensures !Has()
        ensures fresh(this.box)
    {
        box := new BoxedLinear(empty());
    }
    constructor(linear a:A)
        ensures Read() == a
        ensures Has()
        ensures fresh(this.box)
    {
        box := new BoxedLinear(give(a));
    }
    method Take() returns(linear a:A)
        modifies this, box
        requires Has()
        ensures !Has()
        ensures a == old(Read())
    {
        linear var x := box.Swap(empty());
        a := take(x);
    }
    method Give(linear a:A)
        modifies this, box
        requires !Has()
        ensures Has()
        ensures a == Read()
    {
        linear var x := box.Swap(give(a));
        var _ := discard(x);
    }
    function method{:caller_must_be_pure} Borrow():(shared a:A)
        reads this, box
        requires Has()
        ensures a == Read()
    {
        peek(box.Borrow())
    }
}

method MaybeLinearExample<A(00)>(linear a_in:A) returns(linear a:A)
{
    a := a_in;
    var box1 := new MaybeLinear<A>(a);
    var box2 := new MaybeLinear<A>.Empty();
    var box3 := box1; // box1 is not linear, so we can duplicate it
    a := box1.Take();

    // This following would fail, because box3 == box1 and we already took the A out of box1:
    // linear var b := box3.Take();
    // box3.Give(b);
}
